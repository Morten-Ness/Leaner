import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C] [HasZeroMorphisms C]
  [HasZeroObject C]

variable (K L M : HomologicalComplex C c) (φ : K ⟶ L) (φ' : L ⟶ M) (e : c.Embedding c')

variable {j : ι} {j' : ι'} (hj' : e.f j = j') [K.HasHomology j] [L.HasHomology j]
  [(K.extend e).HasHomology j'] [(L.extend e).HasHomology j']

include hj' in
theorem extend_exactAt_iff :
    (K.extend e).ExactAt j' ↔ K.ExactAt j := by
  simp only [HomologicalComplex.exactAt_iff_isZero_homology]
  exact (K.extendHomologyIso e hj').isZero_iff

