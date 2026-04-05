import Mathlib

variable {J : Type v} [Category.{w} J]

theorem kernelIsoKer_hom_comp_subtype {G H : AddCommGrpCat.{u}} (f : G ⟶ H) :
    (AddCommGrpCat.kernelIsoKer f).hom ≫ ofHom (AddSubgroup.subtype f.hom.ker) = kernel.ι f := by ext; rfl

