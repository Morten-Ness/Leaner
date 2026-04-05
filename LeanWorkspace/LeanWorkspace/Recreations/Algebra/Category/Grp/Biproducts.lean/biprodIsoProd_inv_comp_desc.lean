import Mathlib

theorem biprodIsoProd_inv_comp_desc {G H K : AddCommGrpCat.{u}} (f : G ⟶ K) (g : H ⟶ K) :
    (AddCommGrpCat.biprodIsoProd G H).inv ≫ biprod.desc f g =
      ofHom (AddMonoidHom.fst G H) ≫ f + ofHom (AddMonoidHom.snd G H) ≫ g := by
  simp [biprod.desc_eq, ← AddCommGrpCat.biprodIsoProd_inv_comp_fst, ← AddCommGrpCat.biprodIsoProd_inv_comp_snd]

