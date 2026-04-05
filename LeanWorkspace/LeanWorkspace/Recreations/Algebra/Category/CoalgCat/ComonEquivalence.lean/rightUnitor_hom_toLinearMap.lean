import Mathlib

variable {R : Type u} [CommRing R]

variable {M N P Q : Type u} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [AddCommGroup Q]
    [Module R M] [Module R N] [Module R P] [Module R Q] [Coalgebra R M] [Coalgebra R N]
    [Coalgebra R P] [Coalgebra R Q]

theorem rightUnitor_hom_toLinearMap :
    (ρ_ (CoalgCat.of R M)).hom.1.toLinearMap = (TensorProduct.rid R M).toLinearMap := TensorProduct.ext <| by ext; rfl

