import Mathlib

variable {R : Type u} [Ring R]

variable {J : Type} (f : J → ModuleCat.{v} R)

theorem biproductIsoPi_inv_comp_π [Finite J] (f : J → ModuleCat.{v} R) (j : J) :
    (ModuleCat.biproductIsoPi f).inv ≫ biproduct.π f j = ofHom (LinearMap.proj j : (∀ j, f j) →ₗ[R] f j) := IsLimit.conePointUniqueUpToIso_inv_comp _ _ (Discrete.mk j)

