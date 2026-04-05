import Mathlib

variable {G P : Type*}

theorem IsOrderedSMul.smul_le_smul [LE G] [Preorder P] [SMul G P] [IsOrderedSMul G P]
    {a b : G} {c d : P} (hab : a ≤ b) (hcd : c ≤ d) : a • c ≤ b • d := (IsOrderedSMul.smul_le_smul_left _ _ hcd _).trans (IsOrderedSMul.smul_le_smul_right _ _ hab _)

