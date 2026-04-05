import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C] [HasZeroMorphisms C]

variable (K L M : HomologicalComplex C c') (φ : K ⟶ L) (φ' : L ⟶ M)
  (e : c.Embedding c') [e.IsTruncGE]
  [∀ i', K.HasHomology i'] [∀ i', L.HasHomology i'] [∀ i', M.HasHomology i']

variable [HasZeroObject C]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
theorem πTruncGE_naturality :
    K.πTruncGE e ≫ HomologicalComplex.truncGEMap φ e = φ ≫ L.πTruncGE e := by
  apply (e.homEquiv _ _).injective
  ext1
  dsimp [HomologicalComplex.truncGEMap, HomologicalComplex.πTruncGE]
  rw [e.homRestrict_comp_extendMap, e.homRestrict_liftExtend, e.homRestrict_precomp,
    e.homRestrict_liftExtend, HomologicalComplex.restrictionToTruncGE'_naturality]

