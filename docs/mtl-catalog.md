# Catalog of metric temporal properties

Status: catalog, written 2026-11-20 and revised after Codex review round 1. The tick
boxes in section 2 show what is proved or checked. Update them in the same commit as
the theorem or query that changes them. The sources are surveyed in
`docs/standards-overview.md`. The short keys in the source columns (SR2011, HA2010,
CFR862 and others) are listed with links in its section 10,
[References](standards-overview.md#10-references). The plan to prove a subset is
`docs/timing-plan.md` (properties P1 to P7), and the UPPAAL abstraction is
`docs/uppaal-plan.md`.

## 1. Notation and semantics

MTL (metric temporal logic) adds time intervals to the operators of LTL. The catalog
uses MTL with past operators. All interval bounds are in minutes. A parameter that a
source gives in seconds (x s) appears as x/60, and one in hours (x h) as 60·x.

### 1.1 Runs and the two semantics

A run is a finite run of the T2 model (`docs/timing-plan.md` section 3.3): a list of
steps with strictly increasing times. Each step holds environment events (CGM
readings, user boluses) and then at most one loop cycle.

Two semantics are used. Each section of the catalog names its semantics.

- Step semantics (section A). A formula is evaluated at the steps of the run. A
  past operator looks at the steps whose times lie in the interval. Controller
  properties use it, because a cycle only sees the events of earlier steps and of
  its own step.
- Signal semantics (sections B to E). Time is integer milliseconds, as in T2, written
  in minutes. Operators range over all times in the interval. Two kinds of atom
  differ:
  - Event atoms (`cycle`, `reading`, `issue`, `smb`, `acc`, `cmdTemp`, `prevBolus`,
    `bolusStart`, `suspStart`, `occl` and the other pump events) hold exactly at the
    times of their events. They do not persist between events.
  - State observables are functions of time. `rate` is `rateAt` of
    `LeanAID/Time/System.lean`. It changes at steps and also at the deadline of a
    temp, without an event (`tempRate`, line 198). `sched` is `env.sched`. `iob` is
    computed at each time from the doses before it. In section E, `bg` is constant
    between 5-minute CGM samples and takes the new value at each sample time.

| operator | meaning at time t |
|---|---|
| `G I φ` | φ holds at every time (step) in t + I |
| `F I φ` | φ holds at some time (step) in t + I |
| `H I φ` | φ held at every time (step) in t − I |
| `O I φ` | φ held at some time (step) in t − I |
| `φ S ψ` | ψ held at some earlier time, and φ held at every time after it up to t (since) |
| `G φ` | `G[0,∞) φ` |

Intervals carry their endpoints: `[a,b)` includes a and excludes b. The catalog
writes a duration condition "for 15 minutes" as `G[0,15)`. Then a piecewise-constant
signal that holds on exactly [t, t+15) satisfies it.

Finite runs. A past window that reaches before the start of the run has the value
unknown, and a property that needs it is not evaluated at that time. The exception is
a window anchored at the start of the run, written `[0, t − t0]` with t0 the time of
the first step. T2 starts with no CGM readings and no in-run actions. The environment
supplies the initial temp and any pump history before the run. So a window of
readings anchored at the start is complete. So a short log
cannot show hours of inactivity (B10) or a full recovery window (E2). A future
obligation whose window ends after the last step is pending on
an observed run (a log that can continue). A closed run is one where the loop stopped.
There the pump state after the last step is fixed, and `stateAt` decides the
obligation, as in the timing plan. A window of an outcome property (section E) that ends after the run
is not evaluated.

### 1.2 Data binding and operators outside MTL

Some formulas compare a value at a trigger with values later, for example the rate r
of an accepted temp in B2. These are schemas: read them as "for every r, d", with the
values fixed at the trigger. Plain MTL cannot carry a data value forward like this. A
schema over a finite set of values expands to a finite
conjunction of MTL formulas. Accepted durations are whole minutes in {0} ∪ [30, 120]
(`validDuration`, `LeanAID/Time/System.lean:87`), so a schema over d is finite. A
schema over a rational rate r is not. In Lean, a schema is a universally quantified
predicate over runs.

Two operators are outside MTL:

- `Σ[a,b) x`: the insulin delivered from t+a to t+b, in units (U),
- `T[a,b) φ`: the time in minutes during which φ holds in that window.

They come from extensions of STL (signal temporal logic) with averages and
cumulative time. Sections C and E use them. In Lean they are direct predicates over
runs (`integral` in `LeanAID/Time/Run.lean`).

### 1.3 Observables

| name | meaning |
|---|---|
| `cycle` | the loop runs `determine_basal` at this step |
| `preludeOk` | the prelude of `determineBasal` succeeds (`dbPrelude inp = .ok pre`): the inputs pass oref0's own checks |
| `issue(r, d)` | the cycle issues a temp basal of rate r U/h for d minutes (d = 0 cancels) |
| `noCmd` | the cycle issues no rate and no duration (the running temp is kept) |
| `smb(u)` | the cycle issues a microbolus of u U |
| `acc(r, d)` | the pump accepts a temp after validation |
| `cmdTemp` | the pump accepts any temp or cancel. A microbolus alone is not a `cmdTemp` |
| `prevBolus` | an accepted microbolus of an earlier cycle, or a user bolus |
| `bolusStart` | the pump starts a new bolus |
| `noBolusDelivery` | no bolus is being delivered, including an extended bolus that started earlier |
| `reading` | a CGM reading arrives |
| `sched` | the scheduled basal rate, U/h |
| `basal*` | `profileCurrentBasal`: the profile basal rounded to the pump increment (oref0 line 142) |
| `adjBasal` | `pre.basal`: the basal adjusted by the sensitivity ratio. It can be above `sched` |
| `rate` | the pump rate in effect, U/h |
| `curTemp` | the running temp as the cycle input reports it (`currenttemp`), not the pump state |
| `ageRnd` | oref0's `minAgo`: (now − recorded date) in minutes, rounded to 0.1 (F-16) |
| `ageRep` | (now − recorded date) in minutes, not rounded |
| `ageTrue` | (now − true time of the reading) in minutes. The controller does not see it |
| `iob`, `maxIOB`, `maxSafe` | net insulin on board as oref0 computes it, its cap `max_iob`, oref0's `maxSafeBasal` |
| `bg` | glucose in mg/dL: the CGM value in section A, the true value of the virtual patient in section E |

The three ages differ. `ageRnd` is what oref0 compares. `ageRep` is what `p1_derived`
bounds. `ageTrue` is what a clinical freshness requirement means. If the CGM records the true
time, the last two agree.

## 2. Catalog

Placeholders x, y, z, T and W stand for values that the source leaves to the maker.

### 2.1 Tick boxes

Each property has three tick boxes. If the evidence named in the notes column exists
on the branch and passes its check, tick the box. Otherwise leave it open.

| column | evidence that ticks it |
|---|---|
| call | a Lean theorem about one call of `determineBasal` or `LeanAID.step`, checked by `lake build` with no `sorry` |
| run | a Lean theorem about every legal run of the T2 model (`LeanAID/Time/`), checked the same way |
| UPPAAL | a query on the timed-automata model in `uppaal/` with its expected result in `uppaal/results.json`. The result is about the abstract model. The replays of U3a and U3b link model traces to T2 runs, but they are tests, not a proof that the result carries over |

Marks:

| mark | meaning |
|---|---|
| ☑ | proved or checked, for the formula in the row, under the hypotheses that the notes name |
| ◐ | partly: a weaker form, one part, a different observable, or an extra hypothesis that the notes name |
| ☐ | open |
| ✗ | does not hold: a counterexample or a design choice of oref0, named in the notes |
| n/a | does not apply: the layer is not modelled there, or the property is out of scope |

Every Lean theorem assumes valid input (`ValidInput` for one call, `Legal` and
`ValidRun` for runs). The rate and duration theorems hold for finite values. NaN
outputs stay findings (F-06).

### A. Controller output, step semantics

Each property is checked at a cycle and looks back over a bounded past. If the inputs
already summarize the past, a theorem about one call proves the formula.
A theorem about runs also proves that the inputs come from the run.

| ID | property | formula | source | value | call | run | UPPAAL | notes |
|---|---|---|---|---|---|---|---|---|
| A1 | a rate increase or microbolus uses a fresh reading | `G((issue(r,_) ∧ r > basal*) ∨ smb(_) → dated ∧ −5 ≤ ageRnd ≤ 12)` | SR2011 1.3.12, HA2010 3.1.2 | 12 min, chosen by oref0 | ◐ | ◐ | ◐ | call: `cgm_unreliable_no_increase`, for dated readings only. run: `p1_faithful` gives `cgmStale = false`, which an undated reading (NaN age) also passes (F-11). `p1_derived` gives `−5.05 ≤ ageRep < 12.05` if the date is a whole millisecond. UPPAAL: P1 checks the abstraction "has a reading and elapsed time < 723 s", which matches `p1_derived`, not `ageRnd`. F-19: a rate of 0.85 above an unrounded basal of 0.83 is allowed with a stale reading |
| A2 | no increase before the first reading | `G(cycle ∧ ¬O[0, t − t0] reading → ¬(issue(r,_) ∧ r > basal*) ∧ ¬smb(_))`, the history since the start of the run | CFR862 (b)(3)(iv) | | n/a | ☐ | ☑ | UPPAAL: P1 with the `hasReading` guard, and the witness "a cycle before the first reading". The mutation without `hasReading` fails, as a negative control. The UPPAAL flag `hasReading` starts at 0, which matches the anchored window. A stale last reading is A1 |
| A3a | microbolus guard, as oref0 checks it | `G(smb(_) → lastBolusAgeRnd > I)`, with `lastBolusAgeRnd` the rounded age of oref0's `lastBolusTime` | SR2011 1.3.5 (adapted) | I = `SMBInterval`, default 3 min | ☑ | ☑ | n/a | call: `microbolus_limits`. run: `p5_faithful` |
| A3b | microbolus spacing in real time | `G(smb(_) → ¬O[0, I + 0.05) prevBolus)` | SR2011 1.3.5 (adapted) | I whole minutes in 1..10 | n/a | ◐ | ◐ | run: `smb_spacing` gives at least 60000·I + 3000 ms since a real prior bolus, for whole-millisecond `lastBolusTime`, with BolusSeen (oref0's `lastBolusTime` is at or after every prior bolus) as a hypothesis (F-22). A fractional I is not covered. UPPAAL: P5-issued and P5-pair for the instance I = 3 |
| A4 | low glucose suspend | `G(cycle ∧ preludeOk ∧ (bg < thr ∨ minGuardBG < thr) ∧ ¬(bg < thr ∧ minDelta > 0) → ¬smb(_) ∧ (issue(0,_) ∨ (noCmd ∧ curTemp.rate = 0)))` | SR2011 1.3.14, R8, R9 | `thr`: oref0's `threshold`, from `min_bg` | ◐ | ☐ | n/a | call: `low_glucose_suspend`. In the `noCmd` case it proves `curTemp.rate = 0` only if that rate is a binary64 value. The formula needs `preludeOk`, and F-18 shows flat low readings where the prelude path leaves a nonzero basal. `curTemp` is the reported temp, not the pump state |
| A5 | predicted low never raises insulin | `G(cycle ∧ preludeOk ∧ eventualBG < min_bg → (issue(r,_) → 0 ≤ r ≤ adjBasal))` | HA2010 1.1, R10 | `eventualBG` is oref0's `eventualBG'` | ☑ | ☐ | n/a | call: `low_eventual_rate_le_basal`, finite rates. The bound is `adjBasal`, not `sched` |
| A6 | IOB at the cap | `G(cycle ∧ preludeOk ∧ iob ≥ maxIOB → (issue(r,_) → 0 ≤ r ≤ adjBasal) ∧ ¬smb(_))` | SR2011 1.3.16, R11 | | ☑ | ☐ | n/a | call: `iob_at_max`, finite rates and finite `iob`, `max_iob` |
| A7 | rate ceiling | `G(issue(r,_) → 0 ≤ r ≤ roundBasal(maxSafe))` | SR2011 1.2.5, R1, R2 | | ☑ | ☑ | n/a | call: `rate_le_roundBasal_maxSafeBasal`. run: `p2_rate_bound`. Finite rates. F-04, F-06, F-12. UPPAAL abstracts rates to classes |
| A8 | duration bound | `G(issue(r,d) → d = 0 ∨ (r = 0 ∧ 30 ≤ d ≤ 120) ∨ (r ≥ 0 ∧ d = 30))` | SR2011 1.2.5, R4 | 30 to 120 min | ☑ | ☑ | ☑ | call: `issued_temp_ok`. run: `p3_temp_ok`. Finite values (`TempOk`). UPPAAL: P3. NaN durations: F-06 |
| A9 | no microbolus on a large glucose change | `G(cycle ∧ maxDelta > k·bg → ¬smb(_))` | oref0 design. The iCGM rate-of-change criteria motivate it | k = 0.2 by default, at most 0.3 | ☐ | ☐ | n/a | `maxDelta` is the largest of `delta`, `short_avgdelta` and `long_avgdelta` (section 3 gives their computation). Not a requirement in `docs/REQUIREMENTS.md` |
| A10 | a running temp close to the request is kept | `G(cycle ∧ keep → noCmd)`, with `keep`: `curTemp.duration > d − 10`, `curTemp.duration ≤ 120`, `d > 0`, and `0.8·curTemp.rate ≤ rReq ≤ 1.2·curTemp.rate`, where rReq is the requested rate after clamping to `maxSafe` and rounding, and d the requested duration | oref0 design (`setTempBasal`, basal-set-temp.js lines 31 to 34) | | ☐ | ☐ | n/a | `setTempBasal_rate_cases` only lists the possible output rates. It does not show that `keep` selects `noCmd`. DB-09 checks an instance. DB-20 keeps its temp through a different early return of `determine-basal.js` (line 1180, "temp >~ req"). DB-51 is vacuous (F-03) |

### B. Pump execution and alarms, signal semantics

B1 to B4 are in the project's scope as a pump model. B5 to B13 concern pump hardware
and alarms, which `docs/REQUIREMENTS.md` section G puts out of scope. They are listed
so that the catalog is complete.

| ID | property | formula | source | value | call | run | UPPAAL | notes |
|---|---|---|---|---|---|---|---|---|
| B1 | an accepted temp takes effect at once | `G(acc(r,d) ∧ d > 0 → rate = r)` | SR2011 1.2.6. GPCA ("within 500 ms", secondary) | 0 in T2, because a cycle is atomic | n/a | ☑ | n/a | run: `accepted_temp` (the temp starts at the step time) |
| B2 | a temp runs until its deadline, then the schedule | schema over r and d ∈ {30, …, 120}: `G(acc(r,d) ∧ G(0,d) ¬cmdTemp → G[0,d) rate = r)` and `G(acc(r,d) ∧ G(0,d] ¬cmdTemp → G[d,d] rate = sched)` | SR2011 1.2.6. CFR880 (b)(4), as the project's adaptation | d from A8 | n/a | ☑ | ◐ | run: `p4a_expiry`. A microbolus does not end a temp. UPPAAL: P4a checks the rate class (zero, low, high), not the rate value |
| B3 | fallback to the schedule after the loop stops | `G(acc(r,d) ∧ G(0,D] ¬cmdTemp → G[D,D] rate = sched)`, D = 30 if r > 0 and D = 120 if r = 0 | CFR862 (b)(1)(vi), CFR880 (b)(4), as the project's adaptation. Blauw 2016 | D = 30 or 120 | n/a | ☑ | ☑ | run: `temp_bound` and `p4b_fail_safe`, with the hypothesis `InvTemp env.init` (the initial temp obeys the same bound). UPPAAL: P4b-30, P4b-120. F-20: a zero temp can run 120 min after the loop stops |
| B4 | bounded suspension | `G(G[0,S) rate = 0 → F[0,S] alarm)`, or with automatic resume `G(rate = 0 → F[0,S] rate > 0)` | MiniMed 530G (a device feature, not a standard) | S = 120 on the 530G | n/a | ✗ | n/a | oref0 can chain zero temps while glucose stays low. This is a design difference, not a defect. T2 has no alarm |
| B5 | no delivery while suspended | `G(suspended → rate = 0 ∧ noBolusDelivery ∧ ¬bolusStart)` | SR2011 1.8.2, R19 | | n/a | n/a | n/a | T2 has no suspend state. R19 covers the IOB side (tests IOB-15 to IOB-20) |
| B6 | occlusion alarm | `G(occl → F[0,T] alarm)` | SR2011 1.5.5, IEC 60601-2-24, CFR880 (b)(7)(v), FDA TPLC 2014 | T stated by the maker | n/a | n/a | n/a | out of scope |
| B7 | stop flow on occlusion | `G(occl → F[0,x/60] (rate = 0 ∧ noBolusDelivery ∧ alarm))` | SR2011 1.5.5 | x s | n/a | n/a | n/a | out of scope |
| B8 | alarm system delay | `G(cond → F[0,Δ/60] alarm)`, Δ in seconds, the sum of the alarm condition delay and the alarm signal generation delay | IEC 60601-1-8 3.2, 3.10, 6.4.1 (secondary) | if Δ > 10 s, disclose its statistics | n/a | n/a | n/a | out of scope |
| B9 | failsafe on an unrecoverable failure | `G(unrecoverableFail → F[0,x/60] failsafe)` and `G(failsafe → rate = 0 ∧ noBolusDelivery)` | SR2011 3.5.2 | x s | n/a | n/a | n/a | out of scope |
| B10 | stop all delivery on user inactivity | `G(H[0,60x) ¬ui → F[0,ε] (rate = 0 ∧ noBolusDelivery ∧ alarm))` | SR2011 5.4.1 | x h | n/a | n/a | n/a | out of scope. A closed loop runs without user interaction, so this conflicts with AID use |
| B11 | reminders during a pause | `G(suspended ∧ x + y ≤ suspAge ≤ 60z → O[0,y] alarm)`, with `suspAge` the time since the start of the current, uninterrupted suspension | SR2011 1.2.8, 1.8.4, IEC 60601-1-8 3.34 | x, y min, z h | n/a | n/a | n/a | out of scope. `suspAge` resets at each `suspStart`, so a later suspension does not inherit the age of an earlier one |
| B12 | escalation and limited pause | `G(alarm ∧ G[0,x) ¬ack → F[x,x+ε] audible)` and `G(audioPaused → F[0,P] ¬audioPaused)` | SR2011 (escalation), IEC 60601-1-8 3.5, 3.13 | x min, P set by the organization | n/a | n/a | n/a | out of scope |
| B13 | no bolus while alarming | `G(alarm → ¬bolusStart)` | GPCA | | n/a | n/a | n/a | out of scope |

### C. Window sums and averages, signal semantics

These use `Σ`, so they are outside plain MTL.

| ID | property | formula | source | value | call | run | UPPAAL | notes |
|---|---|---|---|---|---|---|---|---|
| C1 | bounded automated delivery | `G(Σ[0,W) autoDelivered ≤ B(W))` for every window length W, where `autoDelivered` counts the temps, the schedule and the microboluses, not user boluses | HA2010 1.1, 2.14, R20 | B(W) in timing-plan section 4.1 | n/a | ◐ | n/a | T2 accepts any positive user bolus, so total delivery has no bound without a cap on user boluses. run: `rate_envelope` and `p6_basal` bound the delivery by temps and schedule by B·W/60, with the hypotheses `RateCap env B`, the schedule at most B at every time, and `InvRate B env.init`. The microbolus term is not proved. It needs BolusSeen (F-22). UPPAAL leaves P6 out |
| C2 | no stacking | `G(cycle ∧ smb(u) → iob + u ≤ maxIOB)`, with `iob` the net IOB computed from all earlier accepted doses (form I1 of R21) | SR2011 1.3.16, HA2010 3.1.3, R21 | | ◐ | ☐ | n/a | call: `microbolus_limits`, up to double rounding (R6). Form I2, with the IOB of microboluses alone, fails: `i2_fails`, F-21 |
| C3 | flow accuracy over windows | for each P in {1, 2, 5, 11, 19, 31}·S: `G(|60·Σ[0,P) delivered / P − r| ≤ e·r)` while the programmed rate r (U/h) is constant | IEC 60601-2-24 trumpet curves (secondary), SR2011 1.1.2, CFR880 (b)(7)(iv) | e stated by the maker | n/a | n/a | n/a | pump hardware, out of scope. Freckmann 2019 reports ±15% in 1 h windows |
| C4 | dose cap per period | `G(Σ[0,1440) delivered ≤ maxDaily)` | Blauw 2016, FDA PCLC 2023 ("total amounts delivered over time") | no number in the sources | n/a | ✗ | n/a | oref0 has no daily cap. It bounds rates and IOB. C1 gives a bound for every window length, which a daily cap can be compared with |
| C5a | DIA lower bound | `dia ≥ 3`, and `dia ≥ 5` for the exponential curves (hours) | HA2010 3.1.3, R16 | | ☑ | n/a | n/a | `curveSetup_dia`. A configuration property, not temporal |
| C5b | one dose: full at the start, zero after the DIA | after a bolus u at t0 with no other dose: `iob = u` at t0, and `G[60·DIA,∞) iob = 0` | HA2010 3.1.3, R17 | | ◐ | n/a | n/a | bilinear curve only. `bilinear_at_zero` gives the dose rounded to a double. `bilinear_after_dia` needs DIA ≤ 1000 h and a relative margin of 2^-50 on the 180-minute point. The exponential curves are not proved |
| C5c | one dose: IOB stays in [0, u] | `G[0,60·DIA] 0 ≤ iob ≤ u` | Blauw 2016, R17 | | ✗ | n/a | n/a | the bilinear polynomial dips below zero just before the DIA: `bilinear_negative`, F-10 |
| C5d | one dose: IOB does not increase | `G[0,∞) (iob at t' ≤ iob at t for t ≤ t')`, a schema over pairs of times | R18 | | ✗ | n/a | n/a | false for the bilinear curve: a 10 U dose with DIA 3 h has IOB below −0.002 U at minute 177 (`bilinear_negative`) and 0 after the DIA (`bilinear_after_dia`), so IOB rises. The Codex review of 2026-11-20 evaluated oref0's `total.js` and found −0.002 U at 177 and 0 U at 180. The exponential curves are open |

### D. Environment assumptions, signal semantics

These are assumptions on the environment, not obligations of the controller. A theorem
that uses one names it as a hypothesis. The T2 theorems in this catalog use none of
them.

| ID | property | formula | source | value |
|---|---|---|---|---|
| D1 | bounded CGM gaps | `G(F[0,M] reading)` | IEEE 11073-10425 ("typically 5 minute", secondary), iCGM (b)(1)(vii), (b)(2) | M from the maker's gap statistics |
| D2 | sensor used only within its life | `G(reading → warmUp ≤ sensorAge ≤ wear)` | iCGM (b)(5), Blauw 2016 (warm-up can exceed 12 h) | wear period claimed by the maker |
| D3 | regular loop cycles | `G(F[0,K] cycle)` | Blauw 2016 (update interval "on the order of 15 min") | oref0 runs about every 5 min. B3 covers a stopped loop without D3 |
| D4 | recorded dates increase and are not in the future | `G(reading with recorded date s → s > every earlier recorded date ∧ s ≤ now)` | HA2010 4.6.1 (clock errors). Anti-replay (DTSec SESIP profile, secondary) is the project's interpretation | T2 lets the recorded date differ from the true time, so T2 does not assume D4. oref0 rejects an increase on a reading dated more than 5 min ahead (A1) |

### E. Clinical outcome on glucose traces, signal semantics

These apply to simulated closed-loop runs (`docs/SIM.md`). There `bg` is the true
glucose of the virtual patient, constant between 5-minute samples. Results on a
simulator are not clinical evidence. The tick column `sim` means a monitor checked
the property on the simulation runs. A check on finite runs is a test, not a proof.
`H = 20160` minutes is 14 days.

| ID | property | formula | source | value | sim | notes |
|---|---|---|---|---|---|---|
| E1 | no level 2 hypoglycaemia event | `G ¬G[0,15) bg < 54` | Danne 2017, Battelino 2019 | 15 min, 54 mg/dL | ☐ | `docs/SIM.md` reports time below 54 mg/dL, but no monitor checks E1 yet |
| E2 | end of a hypoglycaemia event (Danne 2017) | an event that is active just before t is confirmed ended at t if `H(0,15] bg ≥ 70`, which looks at [t−15, t). The event is active from the time its start is confirmed (E1 trigger) until its end is confirmed | Danne 2017 | 15 min, 70 mg/dL for both levels | n/a | a definition, used to count events. Battelino 2023 may differ (secondary) |
| E3 | no prolonged hypoglycaemia | `G ¬G[0,120) bg < 54` | Danne 2017 | 120 min | ☐ | |
| E4 | no level 2 hyperglycaemia event | `G ¬G[0,15) bg > 250` | Battelino 2023 (secondary) | 15 min | ☐ | |
| E5 | no extended hyperglycaemia | `G ¬(T[0,120)(bg > 250) ≥ 90)` | Battelino 2023 (unconfirmed) | 90 of 120 min | ☐ | |
| E6 | time below and in range | `T[0,H)(bg < 54)/H < 0.01`, `T[0,H)(bg < 70)/H < 0.04`, `T[0,H)(70 ≤ bg ≤ 180)/H > 0.70` | Battelino 2019 | 14 days | ☐ | proportions over a horizon, not MTL. `docs/SIM.md` reports these numbers per run, but not as a pass or fail check |
| E7 | settling after a disturbance | after a disturbance at t0, with no other disturbance in [t0, t0+L]: `G[Ts, L] |bg − target| ≤ tol` | IEC 60601-1-10 (settling time, secondary), FDA PCLC tool | Ts, tol stated by the maker. L is the observation horizon | ☐ | the output enters the band by Ts and stays in it up to L |
| E8 | bounded undershoot | after a disturbance at t0: `G[0, L] bg ≥ target − ov` | IEC 60601-1-10 (overshoot, secondary) | stated by the maker | ☐ | |
| E9 | shutoff at low glucose | `G(bg ≤ 70 → rate = 0)` | Kushner 2018 and 2019 (secondary) | 70 mg/dL. A variant at 90 mg/dL was falsified on a published controller | ✗ | `docs/SIM.md`: in the oref0 runs without faults, 79 of the 5,282 steps with true glucose below 54 mg/dL had basal delivered. oref0 decides on the sensor value and on predictions, by design. A4 is the controller-side property |

## 3. Do the oref0 tests express metric temporal properties?

No oref0 test runs a sequence of loop cycles, and no test checks a formula over all
times. Most tests check one function call at one instant. Several IOB tests and the basal
lookup test evaluate one fixed history at several times. So the tests
check finite samples of some temporal properties, but they do not state or check MTL
formulas.

Time enters the tests in five ways.

1. Inputs that summarize the past (`determine-basal.test.js`, 52 active tests as
   mocha counts them, `docs/TESTS.md`). `glucose-get-last.js` computes the glucose
   fields from the readings. It rounds each reading's age to whole minutes and
   divides the change by the age, scaled to mg/dL per 5 minutes. `delta` averages
   the readings with age in (2.5, 7.5) minutes. `short_avgdelta` averages those in
   (2.5, 17.5), and `long_avgdelta` those in (17.5, 42.5). Readings in (−2, 2.5)
   minutes are averaged into the current value. `iob` is a weighted sum of all doses
   over the DIA. These numbers are averages and weighted sums, not MTL formulas. A
   test fixes them as numbers, so it tests the decision as a function of them. The
   correctness of their computation from the history is a separate property (group
   5).

2. Outputs that are commitments over the future. An asserted duration of 30 (or
   "above 29") is the trigger of B2: the pump runs the rate for that time unless a
   new command replaces it. The tests check the number, not the pump behaviour.

3. The remaining time of a past command. In DB-09, a zero temp with 57 minutes left
   is running, and the test expects no command, an instance of A10. In DB-20, a temp
   at or above the requested rate is running with more than 5 minutes left, and an
   early return keeps it. DB-51 means to test a running temp with 29 minutes left,
   but its profile key `"max_bg "` makes the call return an error (F-03). The time is
   in `currenttemp.duration`, not in a clock.

4. One history at several times. The first IOB test (`iob.test.js` lines 10 to 57)
   gives a 2 U bolus at `now` and asserts IOB = 2 at `now`, 0 < IOB < 1.45 and
   0.01 < activity < 0.02 at `now + 60 min`, and IOB = 0 at `now + 3 h` (the DIA).
   These are samples of C5b and C5c. The tests of the other insulin curves do the
   same at their own times, and the test with a 4-hour DIA checks four times. `basal.test.js` looks up the schedule at two times
   of day. The suspend tests (IOB-15 to IOB-20) compare the IOB of two histories, one
   with a suspend and one with the temps shortened by hand. That is a relation between
   two runs, not a property of one run.

5. Computations over a time series. `get-last-glucose.test.js` checks the glucose
   fields of group 1 on fixed series, including two receivers 30 s apart.
   `glucose-noise.js` checks a noise statistic. `cobhistory.test.js` checks that
   duplicate entries are removed.

What the tests leave out. The default `glucose_status` in `determine-basal.test.js`
has no date, so the staleness check never fires there (F-11 is about this case). The
shell test `command-behavior.tests.sh` (lines 250 to 268) runs the command-line
controller on a stale reading and checks that the reason says "BG data is too old".
That is one concrete instance of the stale-data path. It does not check the output
restriction of A1. No JavaScript test covers a stale reading. No test covers
microbolus spacing over time (A3b), temp expiry (B2, B3), lost commands, delivery
over a window (C1) or stacking over cycles (C2). These
properties need a model of runs, which is why the project built T2 and the UPPAAL
abstraction.

Tests by catalog entry. "Asserts" means that the test checks the conclusion of the
row. "Weaker" means that the test checks a weaker conclusion on inputs that the row
covers.

| catalog entry | asserts | weaker |
|---|---|---|
| A4 | DB-23, DB-25 (rate 0) | DB-24 (rate below 0.8) |
| A5 | DB-08, DB-13, DB-14, DB-26 to DB-28, DB-34, DB-64 | |
| A6 | DB-22 | |
| A7 | STB-05 to STB-10 (the clamp in `setTempBasal`) | DB-18 (checks the reason text) |
| A10 | DB-09 | |
| B2 (trigger only) | | every test that asserts `duration` |
| C5b, C5c (samples) | the IOB curve tests | |
| A1 | | the shell test above (reason text only) |
| A2, A3, B3, C1, C2, D, E | none | |
