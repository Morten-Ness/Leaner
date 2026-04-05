import Mathlib

variable {R : Type*}

theorem eq_zero_of_isSumSq_of_neg_isSumSq [NonUnitalNonAssocRing R] [IsFormallyReal R]
    {s : R} (h₁ : IsSumSq s) (h₂ : IsSumSq (-s)) : s = 0 := IsFormallyReal.eq_zero_of_add_right h₁ h₂ (by simp)

