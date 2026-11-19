/-
  LeanAID.Time.Build — legal runs by construction.

  `build` turns a script (times, environment events, and for each cycle the free
  inputs and the outcome) into a run whose cycles take their inputs from the pump
  state, as `LegalCycle` requires. `build_legal` proves that every built run with
  increasing times is legal. The concrete runs of T0 are built this way.

  RESEARCH ARTIFACT. NOT FOR DOSING INSULIN.
-/
import LeanAID.Time.System

namespace LeanAID.Time

open LeanAID

/-- An environment event. -/
inductive EnvEvent where
  | reading (r : Reading)
  | userBolus (u : Rat)

def EnvEvent.toEvent : EnvEvent → Event
  | .reading r => .reading r
  | .userBolus u => .userBolus u

/-- The inputs of a cycle that the run leaves free. -/
structure Free where
  meal_data : Option MealData := some {}
  autosens_data : Option Autosens := none
  microBolusAllowed : Bool := false
  reservoir_data : Reservoir := .undef

/-- One step of a script: environment events, then optionally one cycle. -/
structure ScriptStep where
  time : Int
  env : List EnvEvent := []
  cycle : Option (Free × Outcome) := none

/-- The inputs of a cycle at time `t` in state `s`, as `LegalCycle` fixes them. -/
def inputsAt (env : Env) (s : PState) (t : Int) (f : Free) : DBInputs :=
  { glucose_status := Glucose.getLastGlucose (entries s),
    currenttemp := some (currentTempAt s t),
    iob_data := some (iobInputOf (iobOut env s t f.autosens_data)),
    profile := some (env.profileAt t),
    autosens_data := f.autosens_data, meal_data := f.meal_data,
    microBolusAllowed := f.microBolusAllowed, reservoir_data := f.reservoir_data,
    clock := { now := t, tzOffsetMin := env.tz } }

/-- The cycle event at time `t` in state `s`. -/
def cycleEvent (env : Env) (s : PState) (t : Int) (f : Free) (o : Outcome) : Event :=
  let inp := inputsAt env s t f
  .cycle inp (LeanAID.step inp) o

/-- The events of a script step; the cycle sees the state after the environment events. -/
def stepEvents (env : Env) (s : PState) (ss : ScriptStep) : List Event :=
  let es := ss.env.map EnvEvent.toEvent
  match ss.cycle with
  | none => es
  | some (f, o) => es ++ [cycleEvent env (es.foldl (applyEvent ss.time) s) ss.time f o]

/-- Build a run from a script. Empty steps are dropped. -/
def build (env : Env) : PState → List ScriptStep → Run Event
  | _, [] => []
  | s, ss :: rest =>
    let st : Step Event := { time := ss.time, events := stepEvents env s ss }
    if st.events.isEmpty then build env s rest
    else st :: build env (applyStep s st) rest

theorem legalEvents_env (env : Env) (t : Int) :
    ∀ (s : PState) (es : List EnvEvent) (tail : List Event),
      LegalEvents env t ((es.map EnvEvent.toEvent).foldl (applyEvent t) s) tail →
      LegalEvents env t s ((es.map EnvEvent.toEvent) ++ tail)
  | s, [], tail, h => by simpa using h
  | s, e :: es, tail, h => by
    simp only [List.map_cons, List.cons_append, LegalEvents]
    refine ⟨by cases e <;> trivial, ?_⟩
    apply legalEvents_env env t _ es tail
    simpa [List.foldl] using h

theorem cycleLast_env : ∀ (es : List EnvEvent) (tail : List Event), CycleLast tail → tail.length ≤ 1 →
    CycleLast ((es.map EnvEvent.toEvent) ++ tail)
  | [], tail, h, _ => by simpa using h
  | [e], [], _, _ => by simp [CycleLast]
  | [e], [x], _, _ => by cases e <;> simp [CycleLast, EnvEvent.toEvent, Event.isCycle]
  | [_], _ :: _ :: _, _, hl => by simp at hl
  | e :: e' :: es, tail, h, hl => by
    have ih := cycleLast_env (e' :: es) tail h hl
    simp only [List.map_cons, List.cons_append] at ih ⊢
    exact ⟨by cases e <;> rfl, ih⟩

theorem legal_stepEvents (env : Env) (s : PState) (ss : ScriptStep) :
    CycleLast (stepEvents env s ss) ∧ LegalEvents env ss.time s (stepEvents env s ss) := by
  unfold stepEvents
  cases hc : ss.cycle with
  | none =>
    simp only
    have h1 := cycleLast_env ss.env [] (by simp [CycleLast]) (by simp)
    have h2 := legalEvents_env env ss.time s ss.env [] (by simp [LegalEvents])
    simpa using And.intro h1 h2
  | some fo =>
    obtain ⟨f, o⟩ := fo
    simp only
    refine ⟨cycleLast_env ss.env _ (by simp [CycleLast]) (by simp), ?_⟩
    apply legalEvents_env
    simp only [cycleEvent, LegalEvents, and_true]
    exact { now := rfl, tz := rfl, profile := rfl, iob := rfl, currenttemp := rfl, glucose := rfl, result := rfl }

theorem build_legalFrom (env : Env) : ∀ (s : PState) (sc : List ScriptStep), LegalFrom env s (build env s sc)
  | _, [] => by simp [build, LegalFrom]
  | s, ss :: rest => by
    simp only [build]
    split
    · exact build_legalFrom env s rest
    · rename_i h
      have := legal_stepEvents env s ss
      refine ⟨by simpa using h, this.1, this.2, build_legalFrom env _ rest⟩

theorem build_sub (env : Env) : ∀ (s : PState) (sc : List ScriptStep),
    ∀ st ∈ build env s sc, ∃ ss ∈ sc, st.time = ss.time
  | _, [] => by simp [build]
  | s, ss :: rest => by
    intro st hst
    simp only [build] at hst
    split at hst
    · obtain ⟨ss', h1, h2⟩ := build_sub env s rest st hst
      exact ⟨ss', List.mem_cons_of_mem _ h1, h2⟩
    · simp only [List.mem_cons] at hst
      rcases hst with h | h
      · subst h; exact ⟨ss, List.mem_cons_self .., rfl⟩
      · obtain ⟨ss', h1, h2⟩ := build_sub env _ rest st h
        exact ⟨ss', List.mem_cons_of_mem _ h1, h2⟩

theorem build_increasing (env : Env) : ∀ (s : PState) (sc : List ScriptStep),
    sc.Pairwise (fun a b => a.time < b.time) → Increasing (build env s sc)
  | _, [], _ => by simp [build, Increasing]
  | s, ss :: rest, hp => by
    rw [List.pairwise_cons] at hp
    simp only [build]
    split
    · exact build_increasing env s rest hp.2
    · unfold Increasing
      rw [List.pairwise_cons]
      refine ⟨?_, build_increasing env _ rest hp.2⟩
      intro st hst
      obtain ⟨ss', h1, h2⟩ := build_sub env _ rest st hst
      rw [h2]; exact hp.1 ss' h1

/-- **Built runs are legal** when the script times increase. -/
theorem build_legal (env : Env) (sc : List ScriptStep) (h : sc.Pairwise (fun a b => a.time < b.time)) :
    Legal env (build env env.init sc) :=
  ⟨build_increasing env _ sc h, build_legalFrom env _ sc⟩

end LeanAID.Time
