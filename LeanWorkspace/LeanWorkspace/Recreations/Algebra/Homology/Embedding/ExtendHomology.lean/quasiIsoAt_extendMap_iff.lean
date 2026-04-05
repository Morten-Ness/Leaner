import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C] [HasZeroMorphisms C]
  [HasZeroObject C]

variable (K L M : HomologicalComplex C c) (φ : K ⟶ L) (φ' : L ⟶ M) (e : c.Embedding c')

variable {j : ι} {j' : ι'} (hj' : e.f j = j') [K.HasHomology j] [L.HasHomology j]
  [(K.extend e).HasHomology j'] [(L.extend e).HasHomology j']

include hj' in
theorem quasiIsoAt_extendMap_iff :
    QuasiIsoAt (extendMap φ e) j' ↔ QuasiIsoAt φ j := by
  simp only [quasiIsoAt_iff_isIso_homologyMap]
  exact (MorphismProperty.isomorphisms C).arrow_mk_iso_iff
    (Arrow.isoMk (K.extendHomologyIso e hj') (L.extendHomologyIso e hj'))

