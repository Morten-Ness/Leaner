import Mathlib

variable {R N L M : Type*}

variable [CommRing R] [LieRing L] [LieAlgebra R L]

variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  (c : twoCocycle R L M)

theorem bracket_ofTwoCocycle {c : twoCocycle R L M} (x y : ofTwoCocycle c) :
    letI x₁ := ((LieAlgebra.ofProd c).symm x).1; letI x₂ := ((LieAlgebra.ofProd c).symm x).2
    letI y₁ := ((LieAlgebra.ofProd c).symm y).1; letI y₂ := ((LieAlgebra.ofProd c).symm y).2
    ⁅x, y⁆ = LieAlgebra.ofProd c (⁅x₁, y₁⁆, (c : L →ₗ[R] L →ₗ[R] M) x₁ y₁ + ⁅x₁, y₂⁆ - ⁅y₁, x₂⁆) :=
  rfl

