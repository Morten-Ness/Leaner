import Mathlib

variable {J : Type} [Finite J]

theorem biproductIsoPi_inv_comp_π (f : J → AddCommGrpCat.{u}) (j : J) :
    (AddCommGrpCat.biproductIsoPi f).inv ≫ biproduct.π f j = ofHom (Pi.evalAddMonoidHom (fun j => f j) j) := IsLimit.conePointUniqueUpToIso_inv_comp _ _ (Discrete.mk j)

