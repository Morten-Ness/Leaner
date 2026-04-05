import Mathlib

variable (R : Type*) {S A B : Type*} [CommSemiring R]
  [CommSemiring S] [Semiring A] [Semiring B] [Algebra R S] [Algebra S A] [Algebra S B]
  [Algebra R A] [Algebra R B] [IsScalarTower R S A] [IsScalarTower R S B] [Star A] [Star B]

theorem StarAlgEquiv.restrictScalars_injective :
    Function.Injective (StarAlgEquiv.restrictScalars R : (A ≃⋆ₐ[S] B) → A ≃⋆ₐ[R] B) := fun f g h => StarAlgEquiv.ext fun x =>
    show f.restrictScalars R x = g.restrictScalars R x from DFunLike.congr_fun h x

