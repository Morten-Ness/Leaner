import Mathlib

variable {R : Type u} [CommRing R]

set_option backward.isDefEq.respectTransparency false in
theorem monoidalClosed_pre_app {M N : ModuleCat.{u} R} (P : ModuleCat.{u} R) (f : N ⟶ M) :
    (MonoidalClosed.pre f).app P = ofHom (homLinearEquiv.symm.toLinearMap ∘ₗ
      LinearMap.lcomp _ _ f.hom ∘ₗ homLinearEquiv.toLinearMap) := rfl

