import Mathlib

variable {α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

theorem inf_eq_right {a b : CauSeq α abs} (h : b ≤ a) : a ⊓ b ≈ b := by
  obtain ⟨ε, ε0 : _ < _, i, h⟩ | h := h
  · intro _ _
    refine ⟨i, fun j hj => ?_⟩
    dsimp
    rw [← min_sub_sub_right]
    rwa [sub_self, min_eq_right, abs_zero]
    exact ε0.le.trans (h _ hj)
  · refine Setoid.trans (CauSeq.inf_equiv_inf (Setoid.symm h) (Setoid.refl _)) ?_
    rw [CauSeq.inf_idem]

