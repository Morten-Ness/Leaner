import Mathlib

variable {ι : Type*} {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  {c : ComplexShape ι} {K L M K' L' : HomologicalComplex C c}

theorem isoOfQuasiIsoAt_inv_hom_id (f : K ⟶ L) (i : ι) [K.HasHomology i] [L.HasHomology i]
    [QuasiIsoAt f i] :
    (isoOfQuasiIsoAt f i).inv ≫ homologyMap f i = 𝟙 _ := (isoOfQuasiIsoAt f i).inv_hom_id

