/-
  LeanAID.Proofs.ValidCheck — `validInputB` decides validity soundly.
-/
import LeanAID.Spec.ValidCheck
import LeanAID.Proofs.JsNumLemmas

namespace LeanAID.Proofs

open JsNum

theorem finOf_eq {x : JsNum} {M : Rat} (h : finOf x = some M) : x = .fin M := by
  cases x with
  | nan => cases h
  | fin y => simp [finOf] at h; rw [h]

theorem twoDecimals_sound {x : Rat} (h : twoDecimals x = true) :
    ∃ n : Int, 0 ≤ n ∧ n ≤ 2 ^ 40 ∧ x = Binary64.rd ((n : Rat) / 100) := by
  unfold twoDecimals at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨_, h.1.1, h.1.2, h.2.symm⟩

theorem validProfileB_sound {p : Profile} (h : validProfileB p = true) : ValidProfile p := by
  unfold validProfileB at h
  split at h
  · rename_i cb mb mdb M mi s hcb hmb hmdb hM hmi hs
    have hM' := finOf_eq hM
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h9⟩, h10⟩, d1⟩, d2⟩, d3⟩ := h
    replace h1 := of_decide_eq_true h1
    replace h2 := of_decide_eq_true h2
    replace h3 := of_decide_eq_true h3
    replace h7 := of_decide_eq_true h7
    replace h10 := of_decide_eq_true h10
    refine ⟨⟨cb, hcb, h1⟩, ⟨mb, cb, hmb, hcb, h2⟩, ⟨mdb, cb, hmdb, hcb, h3⟩, ?_, ?_, ?_, ⟨mi, hmi, h7⟩, ?_, ⟨s, hs, h10⟩,
      ?_, ?_⟩
    · intro x hx; rw [hx] at h4; exact of_decide_eq_true h4
    · intro x hx; rw [hx] at h5; exact of_decide_eq_true h5
    · intro amax ha
      rw [ha] at h6
      simp only [Bool.and_eq_true] at h6
      obtain ⟨⟨ha0, ha2⟩, ha3⟩ := h6
      replace ha0 := of_decide_eq_true ha0
      replace ha3 := of_decide_eq_true ha3
      refine ⟨ha0, twoDecimals_sound ha2, ?_⟩
      intro cb' M' hcb' hM''
      rw [hcb] at hcb'; cases hcb'; rw [hM'] at hM''; cases hM''; exact ha3
    · intro x hx; rw [hx] at h9; exact of_decide_eq_true h9
    · intro x hx; rw [hcb] at hx; cases hx; exact of_decide_eq_true d1
    · intro x hx; rw [hmb] at hx; cases hx; exact ⟨of_decide_eq_true d2, of_decide_eq_true d3⟩
  · simp at h

theorem validInputB_sound {inp : DBInputs} (h : validInputB inp = true) : ValidInput inp := by
  unfold validInputB at h
  split at h
  · cases h
  · rename_i p hp
    simp only [Bool.and_eq_true] at h
    obtain ⟨hpv, ha⟩ := h
    refine ⟨⟨p, hp, validProfileB_sound hpv⟩, ?_⟩
    intro p' a hp' ha'
    rw [hp] at hp'; cases hp'
    rw [ha'] at ha
    simp only at ha
    split at ha
    · rename_i r cb M hr hcb hM
      simp only [Bool.and_eq_true] at ha
      refine ⟨r, hr, of_decide_eq_true ha.1, ?_⟩
      intro cb' M' hcb' hM'
      rw [hcb] at hcb'; cases hcb'; rw [finOf_eq hM] at hM'; cases hM'; exact of_decide_eq_true ha.2
    · cases ha

end LeanAID.Proofs
