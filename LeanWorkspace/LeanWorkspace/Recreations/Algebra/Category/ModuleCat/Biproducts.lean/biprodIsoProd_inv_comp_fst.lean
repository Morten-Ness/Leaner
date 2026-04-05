import Mathlib

variable {R : Type u} [Ring R]

theorem biprodIsoProd_inv_comp_fst (M N : ModuleCat.{v} R) :
    (ModuleCat.biprodIsoProd M N).inv ≫ biprod.fst = ofHom (LinearMap.fst R M N) := IsLimit.conePointUniqueUpToIso_inv_comp _ _ (Discrete.mk WalkingPair.left)

