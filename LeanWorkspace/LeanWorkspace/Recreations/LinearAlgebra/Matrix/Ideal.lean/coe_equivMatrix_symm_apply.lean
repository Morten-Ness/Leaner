import Mathlib

variable {R : Type*} (n : Type*)

variable [NonAssocRing R] [Fintype n] [Nonempty n] [DecidableEq n]

theorem coe_equivMatrix_symm_apply (I : TwoSidedIdeal (Matrix n n R)) (i j : n) :
    TwoSidedIdeal.equivMatrix.symm I = {N i j | N ∈ I} := by
  ext r
  constructor
  · intro h
    exact ⟨single i j r, by simpa using h i j, by simp⟩
  · rintro ⟨n, hn, rfl⟩
    rw [SetLike.mem_coe, mem_iff, equivMatrix_symm_apply_ringCon,
      RingCon.coe_ofMatrix_eq_relationMap i j]
    exact ⟨n, 0, (I.mem_iff n).mp hn, rfl, rfl⟩

