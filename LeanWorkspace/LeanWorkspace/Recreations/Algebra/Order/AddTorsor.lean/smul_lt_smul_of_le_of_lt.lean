import Mathlib

variable {G P : Type*}

theorem smul_lt_smul_of_le_of_lt [LE G] [Preorder P] [SMul G P] [IsOrderedCancelSMul G P]
    {a b : G} {c d : P} (h₁ : a ≤ b) (h₂ : c < d) :
    a • c < b • d := by
  refine lt_of_le_of_lt (IsOrderedSMul.smul_le_smul_right a b h₁ c) ?_
  refine lt_of_le_not_ge (IsOrderedSMul.smul_le_smul_left c d (le_of_lt h₂) b) ?_
  by_contra hbdc
  have h : d ≤ c := IsOrderedCancelSMul.le_of_smul_le_smul_left b d c hbdc
  rw [@lt_iff_le_not_ge] at h₂
  simp_all only [not_true_eq_false, and_false]

