import Mathlib

variable {R : Type u} [Ring R]

theorem biprodIsoProd_inv_comp_snd (M N : ModuleCat.{v} R) :
    (ModuleCat.biprodIsoProd M N).inv ≫ biprod.snd = ofHom (LinearMap.snd R M N) := IsLimit.conePointUniqueUpToIso_inv_comp _ _ (Discrete.mk WalkingPair.right)

