import Mathlib

variable {ι : Type*} {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  {c : ComplexShape ι} {K L M K' L' : HomologicalComplex C c}

theorem isoOfQuasiIsoAt_hom_inv_id (f : K ⟶ L) (i : ι) [K.HasHomology i] [L.HasHomology i]
    [QuasiIsoAt f i] :
    homologyMap f i ≫ (isoOfQuasiIsoAt f i).inv = 𝟙 _ := (isoOfQuasiIsoAt f i).hom_inv_id

