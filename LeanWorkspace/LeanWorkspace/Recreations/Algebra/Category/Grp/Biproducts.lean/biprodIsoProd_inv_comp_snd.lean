import Mathlib

theorem biprodIsoProd_inv_comp_snd (G H : AddCommGrpCat.{u}) :
    (AddCommGrpCat.biprodIsoProd G H).inv ≫ biprod.snd = ofHom (AddMonoidHom.snd G H) := IsLimit.conePointUniqueUpToIso_inv_comp _ _ (Discrete.mk WalkingPair.right)

