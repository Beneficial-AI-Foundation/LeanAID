"""Safety monitor for the closed-loop simulation.

At every step it checks, on the actual input and output of the controller, the
requirements of docs/REQUIREMENTS.md that concern a single decision. A violation is a
finding: it is counted and logged, never hidden. Names:

  R1   issued rate <= maxSafeBasal = min(max_basal, 3 x max_daily_basal, 4 x current_basal),
       computed with the max_basal the profile was configured with (so a run whose
       profile lacks max_basal, F-12, is checked against the intended limit)
  R2   issued rate is a finite number >= 0 (a NaN rate prints as null, F-06)
  R4   issued duration is 0 or between 30 and 120 minutes (R4 is not proved)
  SMB  a microbolus was issued although SMB is off in these runs (microBolusAllowed false)
  R6   iob + units <= max_iob for an issued microbolus
  R8   fresh, non-error reading, BG < threshold and minDelta <= 0
       -> a zero temp is issued, or a running zero temp is left in place; no microbolus.
       "Non-error" here excludes error codes and noise but NOT oref0's flat-CGM check
       (delta exactly 0), which the theorem low_glucose_suspend does exclude: the
       monitor checks the stronger requirement on purpose (FINDINGS F-18)
  R9   minGuardBG < threshold (from oref0's reason text) -> the same
  R10  eventualBG < min_bg -> any issued rate <= current_basal (sensitivityRatio is 1 here)
  R11  iob >= max_iob -> any issued rate <= current_basal; no microbolus
  R12  reading stale (> 12 min old or > 5 min in the future, by its TRUE age, which the
       simulator knows even when the entry carries no date, F-11), error-coded (BG <= 10
       or 38) or noisy (noise >= 3) -> any issued rate <= current_basal; no microbolus

threshold = min_bg - 0.5 (min_bg - 40), as determine-basal.js line 329 computes it
(no temp targets or autosens adjustment in these runs). BG, delta and short_avgdelta
come from oref0's getLastGlucose on the same input.
"""
import math
import re

EPS = 1e-9


def _num(x):
    return isinstance(x, (int, float)) and not isinstance(x, bool) and math.isfinite(x)


def iob_equal(a, b):
    """The IOB arrays of oref0 and aid-lean agree on every field aid-lean prints."""
    if not isinstance(a, list) or not isinstance(b, list) or len(a) != len(b):
        return False
    keys = ['iob', 'activity', 'basaliob', 'bolusiob', 'netbasalinsulin', 'bolusinsulin']
    for x, y in zip(a, b):
        for k in keys:
            if x.get(k) != y.get(k):
                return False
        zx, zy = x.get('iobWithZeroTemp') or {}, y.get('iobWithZeroTemp') or {}
        for k in keys:
            if zx.get(k) != zy.get(k):
                return False
    x, y = a[0] if a else {}, b[0] if b else {}
    if x.get('lastBolusTime') != y.get('lastBolusTime'):
        return False
    lx, ly = x.get('lastTemp') or {}, y.get('lastTemp') or {}
    for k in ['date', 'rate', 'duration']:
        if lx.get(k) != ly.get(k):
            return False
    return True


def check(rT, profile, configured_max_basal, glucose, true_age_min, currenttemp, iob, gs):
    v = []
    if 'error' in rT:
        return v
    has_rate = 'rate' in rT
    rate = rT.get('rate')
    dur = rT.get('duration')
    units = rT.get('units')
    cb = profile.get('current_basal')
    mdb = profile.get('max_daily_basal')
    msb = min(configured_max_basal, 3 * mdb, 4 * cb)
    min_bg = profile.get('min_bg')
    max_iob = profile.get('max_iob')
    threshold = min_bg - 0.5 * (min_bg - 40)
    iob_now = iob.get('iob')
    smb = _num(units) and units > 0

    if has_rate:
        if not _num(rate) or rate < 0:
            v.append('R2')
        elif rate > msb + EPS:
            v.append('R1')
        if not (_num(dur) and (dur == 0 or 30 <= dur <= 120)):
            v.append('R4')
    if smb:
        v.append('SMB')
        if _num(iob_now) and iob_now + units > max_iob + EPS:
            v.append('R6')

    bg = gs.get('glucose') if gs else None
    noise = gs.get('noise') if gs else None
    delta = gs.get('delta') if gs else None
    sad = gs.get('short_avgdelta') if gs else None
    stale = true_age_min is None or true_age_min > 12 or true_age_min < -5
    bad = (not _num(bg)) or bg <= 10 or bg == 38 or (_num(noise) and noise >= 3)
    zero_issued = has_rate and _num(rate) and rate == 0 and _num(dur) and dur > 0
    zero_running = (not has_rate) and currenttemp.get('rate') == 0 and currenttemp.get('duration', 0) > 0

    def low_ok():
        return (zero_issued or zero_running) and not smb

    if not stale and not bad and _num(delta) and _num(sad):
        min_delta = min(delta, sad)
        if bg < threshold and min_delta <= 0 and not low_ok():
            v.append('R8')
    m = re.search(r'minGuardBG (-?[0-9.]+)<(-?[0-9.]+)', rT.get('reason', ''))
    if m and float(m.group(1)) < threshold and not low_ok():
        v.append('R9')
    ev = rT.get('eventualBG')
    if _num(ev) and ev < min_bg and has_rate and _num(rate) and rate > cb + EPS:
        v.append('R10')
    if _num(iob_now) and iob_now >= max_iob and ((has_rate and _num(rate) and rate > cb + EPS) or smb):
        v.append('R11')
    if (stale or bad) and ((has_rate and _num(rate) and rate > cb + EPS) or smb):
        v.append('R12')
    return v
