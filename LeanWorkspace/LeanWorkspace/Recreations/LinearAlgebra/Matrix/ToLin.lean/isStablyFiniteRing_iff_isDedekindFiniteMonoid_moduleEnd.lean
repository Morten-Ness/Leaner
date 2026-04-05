import Mathlib

variable (ι : Type*) [Fintype ι] [DecidableEq ι]

variable (R : Type*) [CommSemiring R]

variable (A : Type*) [Semiring A] [Algebra R A]

variable (M : Type*) [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]

theorem isStablyFiniteRing_iff_isDedekindFiniteMonoid_moduleEnd :
    IsStablyFiniteRing A ↔ ∀ n, IsDedekindFiniteMonoid (Module.End A (Fin n → A)) := by
  simp_rw [isStablyFiniteRing_iff, MulEquivClass.isDedekindFiniteMonoid_iff
    (matrixRingEquivEndVecMulOpposite (ι := Fin _) (A := A)),
    MulOpposite.isDedekindFiniteMonoid_iff]

