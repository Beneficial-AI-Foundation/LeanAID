# Draft issue for Artificial-Pancreas/iAPS (F-04), not sent

**Title:** Temp basal can be set slightly above the Max Basal limit after rounding

**Where:** the oref JS in iAPS, `FreeAPS/Resources/javascript/bundle/basal-set-temp.js`
(`setTempBasal`), built from `lib/basal-set-temp.js` and `lib/round-basal.js`. That source is, as
far as we can tell, the `iaps` branch of Artificial-Pancreas/oref0 (@ 10bdfe3), which has the same
code. Checked on iAPS `main` @ 486f85b and `dev` @ ea425ea (identical bundles).

### What happens

`setTempBasal` caps the requested rate at `maxSafeBasal`
(`min(max_basal, 3 × max_daily_basal, 4 × current_basal)`) and then rounds it to the *nearest*
pump step. When the limit is not a multiple of the step, the rounded rate is above the limit.

### Reproduction

Against the shipped bundle (loaded as iAPS does, with `freeaps_basalSetTemp`):
`setTempBasal(2, 30, {current_basal: 0.5, max_basal: 0.83, max_daily_basal: 1}, {}, {})` returns
**0.85 U/h**. With `max_basal` 2.33 (and `current_basal` 1, `max_daily_basal` 1.2), a high request
is issued as **2.35 U/h**. The same happens end to end through `freeaps_determineBasal`.

### Can it happen in iAPS?

Yes. Max Basal is entered in a free decimal field (`PumpSettingsEditorRootView.swift:38-42`, with a
`.decimal` `NumberFormatter` and no step), so values such as 0.83 or 2.33 can be stored. In closed
loop, `APSManager.enactSuggested` sends the algorithm's rate to the pump unchanged
(`APSManager.swift:815-818`). The `min(rate, maxBasal)` at `:522-523` is in the manual
`enactTempBasal` path only.

### Why it matters (our estimate: low)

The excess is at most half a pump step (≤ 0.025 U/h). But Max Basal is a user-set hard limit, and
the closed loop has no other app-side cap behind it.

### Suggested fix

In the JS source, after rounding, if the result exceeds `maxSafeBasal`, round `maxSafeBasal` down
to the pump step (patch for the `iaps` source: `docs/upstream/forks/Artificial-Pancreas-oref0/F-04.patch`,
the same change as proposed to openaps/oref0). We also tested the equivalent change directly on the
minified bundle (`docs/upstream/iaps/F-04-bundle.patch`): 0.83 → 0.80 U/h. Over 3,944,160
`setTempBasal` inputs, the patched bundle never exceeds `maxSafeBasal`, and it differs from the
original only where the original did. Alternatively (or as well), the Swift side could cap the
enacted rate at `pumpSettings.maxBasal` in `enactSuggested`, as the manual path already does, and
round down with the pump's supported rates.

---
Found while transcribing oref0 into Lean 4 (LeanAID, Beneficial AI Foundation).
