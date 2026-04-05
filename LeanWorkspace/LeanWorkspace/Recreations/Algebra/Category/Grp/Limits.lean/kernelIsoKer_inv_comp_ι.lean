import Mathlib

variable {J : Type v} [Category.{w} J]

theorem kernelIsoKer_inv_comp_ι {G H : AddCommGrpCat.{u}} (f : G ⟶ H) :
    (AddCommGrpCat.kernelIsoKer f).inv ≫ kernel.ι f = ofHom (AddSubgroup.subtype f.hom.ker) := by
  simp [AddCommGrpCat.kernelIsoKer]

