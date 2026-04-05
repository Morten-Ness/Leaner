import Mathlib

variable {M G α : Type*}

theorem FaithfulSMul.tower_bot (R S T : Type*) [Monoid S] [MulOneClass T]
    [SMul R S] [SMul R T] [MulAction S T]
    [IsScalarTower R S S] [IsScalarTower R T T]
    [IsScalarTower R S T] [FaithfulSMul R T] : FaithfulSMul R S := by
  rw [faithfulSMul_iff_injective_smul_one]
  refine .of_comp (f := (· • (1 : T))) ?_
  simpa [Function.comp_def, one_smul, ← faithfulSMul_iff_injective_smul_one]

