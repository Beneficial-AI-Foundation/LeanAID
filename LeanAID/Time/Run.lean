import LeanAID.Proofs.Rounding

/-!
# Runs over time

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

open LeanAID.Proofs

/-- One step of a run: an ordered list of events at one time. -/
structure Step (ε : Type) where
  /-- epoch milliseconds, as `clock.now` -/
  time : Int
  /-- the events, in order. The legal-run predicate requires the list nonempty. -/
  events : List ε
  deriving Repr

/-- A run: a finite list of steps. Legal runs list them in increasing time. -/
abbrev Run (ε : Type) := List (Step ε)

variable {ε σ : Type}

/-- Step times are strictly increasing. -/
def Increasing (r : Run ε) : Prop := r.Pairwise (fun a b => a.time < b.time)

/-- The steps at or before time `t`. On an increasing run this is a prefix. -/
def upTo (r : Run ε) (t : Int) : Run ε := r.filter (fun s => decide (s.time ≤ t))

/-- The state after the steps at or before `t`, from an initial state and a step
    function. -/
def stateAt (init : σ) (upd : σ → Step ε → σ) (r : Run ε) (t : Int) : σ :=
  (upTo r t).foldl upd init

/-! ### The integral of a rate over milliseconds

A rate in U/h that is constant on every millisecond `[k, k + 1)` has the integral
`Σ_{k=a}^{b-1} f k / 3 600 000` units over `[a, b)`. Every rate in the pump model
changes only at integer milliseconds, so this sum is the exact integral. -/

/-- Milliseconds per hour. -/
def msPerHour : Rat := 3600000

/-- `Σ_{i<n} f (a + i)`. -/
def sumFrom (f : Int → Rat) (a : Int) : Nat → Rat
  | 0 => 0
  | n + 1 => sumFrom f a n + f (a + n)

/-- The insulin in U delivered over `[a, a + n)` ms by a rate `f` in U/h:
    `Σ_{i<n} f(a + i) / msPerHour`. -/
def integral (f : Int → Rat) (a : Int) (n : Nat) : Rat := sumFrom f a n / msPerHour

theorem sumFrom_mono {f g : Int → Rat} (a : Int) (h : ∀ k, a ≤ k → f k ≤ g k) :
    ∀ n, sumFrom f a n ≤ sumFrom g a n
  | 0 => Rat.le_refl
  | n + 1 => by
    simp only [sumFrom]
    have := sumFrom_mono a h n
    have := h (a + n) (by omega)
    grind

theorem sumFrom_const (c : Rat) (a : Int) : ∀ n, sumFrom (fun _ => c) a n = c * n
  | 0 => by simp [sumFrom]
  | n + 1 => by
    simp only [sumFrom, sumFrom_const c a n]
    push_cast; grind

/-- If `f k ≤ c` for all `k ≥ a`, then `integral f a n ≤ c · n / msPerHour`. -/
theorem integral_le_const {f : Int → Rat} {c : Rat} (a : Int) (n : Nat) (h : ∀ k, a ≤ k → f k ≤ c) :
    integral f a n ≤ c * n / msPerHour := by
  unfold integral
  have := sumFrom_mono (f := f) (g := fun _ => c) a h n
  rw [sumFrom_const] at this
  exact div_le_div_of_le (by unfold msPerHour; decide) this

end LeanAID.Time
