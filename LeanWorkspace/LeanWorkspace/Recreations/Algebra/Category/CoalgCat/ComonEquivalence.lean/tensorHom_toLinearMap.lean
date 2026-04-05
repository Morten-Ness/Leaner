import Mathlib

variable {R : Type u} [CommRing R]

variable {M N P Q : Type u} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [AddCommGroup Q]
    [Module R M] [Module R N] [Module R P] [Module R Q] [Coalgebra R M] [Coalgebra R N]
    [Coalgebra R P] [Coalgebra R Q]

theorem tensorHom_toLinearMap (f : M →ₗc[R] N) (g : P →ₗc[R] Q) :
    (CoalgCat.ofHom f ⊗ₘ CoalgCat.ofHom g).1.toLinearMap
      = TensorProduct.map f.toLinearMap g.toLinearMap := rfl

