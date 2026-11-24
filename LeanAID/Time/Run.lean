import LeanAID.Proofs.Rounding
import MetricTemporal.Run.Run
import MetricTemporal.Run.Integral

/-!
# Runs over time

The generic definitions are in the library `MetricTemporal` (`MetricTemporal/Run/`). This
file fixes the unit and exports the names that LeanAID uses.

Time is `Int` epoch milliseconds, the unit of `clock.now`. Let `ε` be an event type.

- A `Step ε` is an ordered list of events at one time; a `Run ε` is a finite list of steps.
- `Increasing r` states that the step times of `r` are strictly increasing.
- `stateAt init upd r t` folds `upd` over the steps of `r` at or before `t`.
- `integral f a n` is the insulin, in U, delivered over `[a, a + n)` by a rate `f` in U/h
  that is constant on every millisecond.

**Theorem** (`integral_le_const`). If `f k ≤ c` for all `k ≥ a`, then
`integral f a n ≤ c · n / msPerHour`.

Research artifact. Not for dosing insulin.
-/

namespace LeanAID.Time

export MetricTemporal (Step Run Increasing upTo stateAt upTo_split upTo_take
  sumFrom sumFrom_mono sumFrom_const)

/-- Milliseconds per hour. -/
def msPerHour : Rat := 3600000

/-- The insulin in U delivered over `[a, a + n)` ms by a rate `f` in U/h:
    `Σ_{i<n} f(a + i) / msPerHour`. -/
def integral (f : Int → Rat) (a : Int) (n : Nat) : Rat := MetricTemporal.integral msPerHour f a n

/-- If `f k ≤ c` for all `k ≥ a`, then `integral f a n ≤ c · n / msPerHour`. -/
theorem integral_le_const {f : Int → Rat} {c : Rat} (a : Int) (n : Nat) (h : ∀ k, a ≤ k → f k ≤ c) :
    integral f a n ≤ c * n / msPerHour :=
  MetricTemporal.integral_le_const (by unfold msPerHour; decide) a n h

end LeanAID.Time
