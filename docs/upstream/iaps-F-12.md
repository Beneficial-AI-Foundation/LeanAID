# Draft issue for Artificial-Pancreas/iAPS (F-12), not sent

**Title:** If middleware leaves max_basal (or max_daily_basal / current_basal) non-numeric, no basal cap is applied

**Where:** the oref JS in iAPS, `FreeAPS/Resources/javascript/bundle/basal-set-temp.js`
(`getMaxSafeBasal` / `setTempBasal`), built from `lib/basal-set-temp.js` (as far as we can tell,
the `iaps` branch of Artificial-Pancreas/oref0 @ 10bdfe3, which has the same code). Checked on iAPS
`main` @ 486f85b and `dev` @ ea425ea.

### What happens

`getMaxSafeBasal` returns `Math.min(max_basal, 3 * max_daily_basal, 4 * current_basal)`. If any of
the three is missing or not a number, the result is `NaN`, and `rate > maxSafeBasal` is always
false, so the requested rate is issued uncapped.

### Reproduction

Against the shipped bundles (`freeaps_determineBasal`, `freeaps_basalSetTemp`), with oref0's test
profile (current basal 0.9, `max_daily_basal` 1.3, `max_basal` 3.5), BG 300 rising 10 mg/dL per
5 min, IOB 0:

- complete profile: 3.5 U/h (capped at `max_basal`);
- the same profile without `max_basal` (or without `max_daily_basal`, or both): **5.9 U/h**.

### Can it happen in iAPS?

Not through the normal settings: `max_basal` comes from `PumpSettings.maxBasal`, a non-optional
`Decimal`. But iAPS runs the user's middleware JS on the profile before determine-basal
(`OpenAPS.swift:108-119`; `prepare/middleware.js:15` calls `middleware(…, profile, …)` and
returns the same object, line 33). A middleware that deletes or miscomputes one of these fields
(e.g. `profile.max_basal = profile.maxBasal` with a typo, or arithmetic on an undefined field)
removes the cap. In closed loop, the rate then goes to the pump unchanged
(`APSManager.swift:815-818`); the `min(rate, maxBasal)` at `:522-523` is only in the manual path.

### Why it matters (our estimate: low likelihood, large effect)

It needs a user-written middleware mistake, but the effect is a basal rate with no app-side
limit (6.6 × the scheduled basal in the reproduction).

### Suggested fix

In the JS source, if `maxSafeBasal` is not a finite positive number, do not raise the rate. Cap
at `current_basal` and report the error, or cancel the temp if that is invalid too (patch for the
`iaps` source: `docs/upstream/forks/Artificial-Pancreas-oref0/F-12.patch`, the same change as
proposed to openaps/oref0). We also tested it directly on the minified bundle
(`docs/upstream/iaps/F-12-bundle.patch`): the reproduction gives 0.9 U/h, and the complete profile
is unchanged. Independently, `enactSuggested` could apply `min(rate, pumpSettings.maxBasal)` as the
manual path does, so that no JS-side mistake can exceed Max Basal.

---
Found while transcribing oref0 into Lean 4 (LeanAID, Beneficial AI Foundation).
