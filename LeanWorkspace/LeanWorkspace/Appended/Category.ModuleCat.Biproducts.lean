import Mathlib

section

variable {R : Type u} [Ring R]

theorem biprodIsoProd_inv_comp_fst (M N : ModuleCat.{v} R) :
    (ModuleCat.biprodIsoProd M N).inv ≫ biprod.fst = ofHom (LinearMap.fst R M N) := IsLimit.conePointUniqueUpToIso_inv_comp _ _ (Discrete.mk WalkingPair.left)

end

section

variable {R : Type u} [Ring R]

theorem biprodIsoProd_inv_comp_snd (M N : ModuleCat.{v} R) :
    (ModuleCat.biprodIsoProd M N).inv ≫ biprod.snd = ofHom (LinearMap.snd R M N) := IsLimit.conePointUniqueUpToIso_inv_comp _ _ (Discrete.mk WalkingPair.right)

end

section

variable {R : Type u} [Ring R]

variable {J : Type} (f : J → ModuleCat.{v} R)

theorem biproductIsoPi_inv_comp_π [Finite J] (f : J → ModuleCat.{v} R) (j : J) :
    (ModuleCat.biproductIsoPi f).inv ≫ biproduct.π f j = ofHom (LinearMap.proj j : (∀ j, f j) →ₗ[R] f j) := IsLimit.conePointUniqueUpToIso_inv_comp _ _ (Discrete.mk j)

end
