import Mathlib

variable {R : Type u} [CommRing R]

variable {M N P Q : Type u} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [AddCommGroup Q]
    [Module R M] [Module R N] [Module R P] [Module R Q] [Coalgebra R M] [Coalgebra R N]
    [Coalgebra R P] [Coalgebra R Q]

theorem leftUnitor_hom_toLinearMap :
    (λ_ (CoalgCat.of R M)).hom.1.toLinearMap = (TensorProduct.lid R M).toLinearMap := TensorProduct.ext <| by ext; rfl

