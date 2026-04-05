import Mathlib

variable {G P : Type*}

theorem smul_lt_smul_of_lt_of_le [Preorder G] [Preorder P] [SMul G P] [IsOrderedCancelSMul G P]
    {a b : G} {c d : P} (h₁ : a < b) (h₂ : c ≤ d) : a • c < b • d := by
  refine lt_of_le_of_lt (IsOrderedSMul.smul_le_smul_left c d h₂ a) ?_
  refine lt_of_le_not_ge (IsOrderedSMul.smul_le_smul_right a b (le_of_lt h₁) d) ?_
  by_contra hbad
  have h : b ≤ a := IsOrderedCancelSMul.le_of_smul_le_smul_right b a d hbad
  rw [@lt_iff_le_not_ge] at h₁
  simp_all only [not_true_eq_false, and_false]

