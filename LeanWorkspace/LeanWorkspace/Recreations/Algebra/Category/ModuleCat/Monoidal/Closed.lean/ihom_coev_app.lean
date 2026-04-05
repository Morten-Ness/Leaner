import Mathlib

variable {R : Type u} [CommRing R]

set_option backward.isDefEq.respectTransparency false in
theorem ihom_coev_app (M N : ModuleCat.{u} R) :
    (ihom.coev M).app N = ModuleCat.ofHom₂ (TensorProduct.mk _ _ _).flip := rfl

