"""Suggested fixes for F-04, F-11, F-12 as exact text replacements on oref0-style lib/.
usage: python3 -I fixes.py <finding> <lib dir>   (edits files in place; prints files touched)
Each replacement must match exactly once, otherwise the script fails and changes nothing."""
import sys, os

F04 = [
 ('round-basal.js',
  "var round_basal = function round_basal(basal, profile) {\n",
  "var round_basal = function round_basal(basal, profile, direction) {\n"
  "\n"
  "    // direction 'down': round down to the pump increment (never above basal)\n"
  "    var r = (direction === 'down') ? function (x) { return Math.floor(x + 1e-9); } : Math.round;\n"),
 ('round-basal.js', "rounded_basal = Math.round(basal * lowest_rate_scale) / lowest_rate_scale;",
                    "rounded_basal = r(basal * lowest_rate_scale) / lowest_rate_scale;"),
 ('round-basal.js', "rounded_basal = Math.round(basal * 20) / 20;", "rounded_basal = r(basal * 20) / 20;"),
 ('round-basal.js', "rounded_basal = Math.round(basal * 10) / 10;", "rounded_basal = r(basal * 10) / 10;"),
 ('basal-set-temp.js',
  "    var suggestedRate = round_basal(rate, profile);\n",
  "    var suggestedRate = round_basal(rate, profile);\n"
  "    // rounding to the nearest pump increment can go above maxSafeBasal when maxSafeBasal\n"
  "    // is not on the pump's grid (e.g. 0.83 -> 0.85): round down instead\n"
  "    if (suggestedRate > maxSafeBasal) {\n"
  "        suggestedRate = round_basal(maxSafeBasal, profile, 'down');\n"
  "    }\n"),
]

# F-11: every form of the check is rewritten so that NaN counts as stale.
F11_FORMS = [
 ("minAgo > 12 || minAgo < -5", "!(minAgo <= 12 && minAgo >= -5)"),
 ("minAgo > 12", "!(minAgo <= 12)"),
]
F11 = 'F11'

F12 = [
 ('basal-set-temp.js',
  "    var maxSafeBasal = tempBasalFunctions.getMaxSafeBasal(profile);\n",
  "    var maxSafeBasal = tempBasalFunctions.getMaxSafeBasal(profile);\n"
  "    if (!(typeof maxSafeBasal === 'number' && isFinite(maxSafeBasal) && maxSafeBasal > 0)) {\n"
  "        // max_basal, max_daily_basal or current_basal is missing or invalid, so there is no\n"
  "        // safety limit: never go above the scheduled basal (low temps are still allowed)\n"
  "        var cb = profile.current_basal;\n"
  "        reason(rT, 'Error: maxSafeBasal ' + maxSafeBasal + ' is not a positive number; check max_basal, max_daily_basal and current_basal');\n"
  "        if (!(typeof cb === 'number' && isFinite(cb) && cb > 0)) {\n"
  "            reason(rT, 'canceling temp');\n"
  "            rT.duration = 0;\n"
  "            rT.rate = 0;\n"
  "            return rT;\n"
  "        }\n"
  "        maxSafeBasal = cb;\n"
  "    }\n"),
]

FIXES = {'F-04': F04, 'F-11': F11, 'F-12': F12}

def main():
    finding, lib = sys.argv[1], sys.argv[2]
    texts = {}
    if FIXES[finding] == 'F11':
        p = os.path.join(lib, 'determine-basal/determine-basal.js')
        t = open(p).read(); n = 0
        for old, new in F11_FORMS:
            n += t.count(old); t = t.replace(old, new)
        if n == 0 or 'minAgo > 12' in t:
            sys.exit('F-11: check not found or not fully rewritten')
        open(p, 'w').write(t); print(p, n, 'sites'); return
    for rel, old, new in FIXES[finding]:
        p = os.path.join(lib, rel)
        s = texts.get(p) or open(p).read()
        n = s.count(old)
        if n != 1:
            sys.exit('%s: expected 1 match in %s, found %d: %r' % (finding, rel, n, old[:60]))
        texts[p] = s.replace(old, new)
    for p, s in texts.items():
        open(p, 'w').write(s)
        print(p)

main()
