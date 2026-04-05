import Mathlib

variable {R : Type u} [CommRing R]

variable {M N P Q : Type u} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [AddCommGroup Q]
    [Module R M] [Module R N] [Module R P] [Module R Q] [Coalgebra R M] [Coalgebra R N]
    [Coalgebra R P] [Coalgebra R Q]

theorem associator_hom_toLinearMap :
    (α_ (CoalgCat.of R M) (CoalgCat.of R N) (CoalgCat.of R P)).hom.1.toLinearMap
      = (TensorProduct.assoc R M N P).toLinearMap := TensorProduct.ext <| TensorProduct.ext <| by ext; rfl

