/-
  LeanAID.Time.Run — runs over time (docs/timing-plan.md, section 3.3, item T1).

  Time is `Int` milliseconds since the epoch, the unit of `clock.now`. A run is a
  finite list of steps with strictly increasing times. A step is an ordered list
  of events at one time. What the events are is fixed by the transition system
  (`LeanAID.Time.System`); this file is generic in the event type.

  Also here: the state at a time `t` (a fold over the steps at or before `t`) and
  the integral of a rate over a half-open interval of milliseconds.

  Lean core only. RESEARCH ARTIFACT. NOT FOR DOSING INSULIN.
-/
import LeanAID.Proofs.Rounding

namespace LeanAID.Time

open LeanAID.Proofs

/-- One step of a run: an ordered list of events at one time. -/
structure Step (ε : Type) where
  /-- epoch milliseconds, as `clock.now` -/
  time : Int
  /-- the events, in order. The legal-run predicate requires the list nonempty. -/
  events : List ε
  deriving Repr

/-- A finite run. -/
abbrev Run (ε : Type) := List (Step ε)

/-- Whether more steps may follow a finite run. On a closed run (for example a
    stopped loop) every deadline after the last step is decided by the state at
    that time. On an observed run (a log that can continue) such deadlines are
    pending. -/
inductive Status where
  | closed
  | observed
  deriving Repr, DecidableEq

variable {ε σ : Type}

/-- Step times are strictly increasing. -/
def Increasing (r : Run ε) : Prop := r.Pairwise (fun a b => a.time < b.time)

/-- The steps at or before time `t`. On an increasing run this is a prefix. -/
def upTo (r : Run ε) (t : Int) : Run ε := r.filter (fun s => decide (s.time ≤ t))

/-- The steps strictly before time `t`. -/
def before (r : Run ε) (t : Int) : Run ε := r.filter (fun s => decide (s.time < t))

/-- The state after the steps at or before `t`, from an initial state and a step
    function. -/
def stateAt (init : σ) (upd : σ → Step ε → σ) (r : Run ε) (t : Int) : σ :=
  (upTo r t).foldl upd init

/-- The state just before time `t` (after the steps strictly before `t`). -/
def stateBefore (init : σ) (upd : σ → Step ε → σ) (r : Run ε) (t : Int) : σ :=
  (before r t).foldl upd init

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

/-- The insulin (units) delivered over `[a, a + n)` ms at the rate `f` (U/h). -/
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

theorem sumFrom_nonneg {f : Int → Rat} (a : Int) (h : ∀ k, 0 ≤ f k) : ∀ n, 0 ≤ sumFrom f a n
  | 0 => Rat.le_refl
  | n + 1 => by
    simp only [sumFrom]
    have := sumFrom_nonneg a h n
    have := h (a + n)
    grind

/-- Splitting an interval: `[a, a + m + n) = [a, a + m) ∪ [a + m, a + m + n)`. -/
theorem sumFrom_add (f : Int → Rat) (a : Int) (m : Nat) : ∀ n,
    sumFrom f a (m + n) = sumFrom f a m + sumFrom f (a + m) n
  | 0 => by simp only [sumFrom, Nat.add_zero]; grind
  | n + 1 => by
    rw [← Nat.add_assoc]
    simp only [sumFrom, sumFrom_add f a m n]
    have : a + ((m + n : Nat) : Int) = a + m + n := by push_cast; omega
    rw [this]; grind

/-- A pointwise bound on the rate bounds the integral. -/
theorem integral_le_const {f : Int → Rat} {c : Rat} (a : Int) (n : Nat) (h : ∀ k, a ≤ k → f k ≤ c) :
    integral f a n ≤ c * n / msPerHour := by
  unfold integral
  have := sumFrom_mono (f := f) (g := fun _ => c) a h n
  rw [sumFrom_const] at this
  exact div_le_div_of_le (by unfold msPerHour; decide) this

theorem integral_nonneg {f : Int → Rat} (a : Int) (n : Nat) (h : ∀ k, 0 ≤ f k) : 0 ≤ integral f a n := by
  unfold integral
  exact div_nonneg' (by unfold msPerHour; decide) (sumFrom_nonneg a h n)

end LeanAID.Time
