import Mathlib

theorem biprodIsoProd_inv_comp_fst (G H : AddCommGrpCat.{u}) :
    (AddCommGrpCat.biprodIsoProd G H).inv ≫ biprod.fst = ofHom (AddMonoidHom.fst G H) := IsLimit.conePointUniqueUpToIso_inv_comp _ _ (Discrete.mk WalkingPair.left)

