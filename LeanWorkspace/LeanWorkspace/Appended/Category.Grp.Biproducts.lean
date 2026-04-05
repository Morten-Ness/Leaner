import Mathlib

section

theorem biprodIsoProd_inv_comp_desc {G H K : AddCommGrpCat.{u}} (f : G ⟶ K) (g : H ⟶ K) :
    (AddCommGrpCat.biprodIsoProd G H).inv ≫ biprod.desc f g =
      ofHom (AddMonoidHom.fst G H) ≫ f + ofHom (AddMonoidHom.snd G H) ≫ g := by
  simp [biprod.desc_eq, ← AddCommGrpCat.biprodIsoProd_inv_comp_fst, ← AddCommGrpCat.biprodIsoProd_inv_comp_snd]

end

section

theorem biprodIsoProd_inv_comp_fst (G H : AddCommGrpCat.{u}) :
    (AddCommGrpCat.biprodIsoProd G H).inv ≫ biprod.fst = ofHom (AddMonoidHom.fst G H) := IsLimit.conePointUniqueUpToIso_inv_comp _ _ (Discrete.mk WalkingPair.left)

end

section

theorem biprodIsoProd_inv_comp_snd (G H : AddCommGrpCat.{u}) :
    (AddCommGrpCat.biprodIsoProd G H).inv ≫ biprod.snd = ofHom (AddMonoidHom.snd G H) := IsLimit.conePointUniqueUpToIso_inv_comp _ _ (Discrete.mk WalkingPair.right)

end

section

variable {J : Type} [Finite J]

theorem biproductIsoPi_inv_comp_π (f : J → AddCommGrpCat.{u}) (j : J) :
    (AddCommGrpCat.biproductIsoPi f).inv ≫ biproduct.π f j = ofHom (Pi.evalAddMonoidHom (fun j => f j) j) := IsLimit.conePointUniqueUpToIso_inv_comp _ _ (Discrete.mk j)

end
