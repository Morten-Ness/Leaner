import Mathlib

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

variable {v : K} {q : ℚ}

theorem of_terminates_iff_of_rat_terminates {v : K} {q : ℚ} (v_eq_q : v = (q : K)) :
    (of v).Terminates ↔ (of q).Terminates := by
  constructor <;> intro h <;> obtain ⟨n, h⟩ := h <;> use n <;>
    simp only [Stream'.Seq.TerminatedAt, (GenContFract.coe_of_s_get?_rat_eq v_eq_q n).symm] at h ⊢ <;>
    cases h' : (of q).s.get? n <;>
    simp only [h'] at h <;>
    trivial

