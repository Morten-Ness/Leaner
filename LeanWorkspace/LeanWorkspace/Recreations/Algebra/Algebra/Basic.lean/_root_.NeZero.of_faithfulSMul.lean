import Mathlib

open scoped Algebra

theorem _root_.NeZero.of_faithfulSMul (R A : Type*) [Semiring R] [Semiring A] [Module R A]
    [IsScalarTower R A A] [FaithfulSMul R A] (n : ℕ) [NeZero (n : R)] :
    NeZero (n : A) := NeZero.nat_of_injective (f := ringHomEquivModuleIsScalarTower.symm ⟨_, ‹_›⟩) <|
    (faithfulSMul_iff_injective_smul_one R A).mp ‹_›

