import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C] [HasZeroMorphisms C]
  [HasZeroObject C]

variable (K L M : HomologicalComplex C c) (φ : K ⟶ L) (φ' : L ⟶ M) (e : c.Embedding c')

variable {j : ι} {j' : ι'} (hj' : e.f j = j') [K.HasHomology j] [L.HasHomology j]
  [(K.extend e).HasHomology j'] [(L.extend e).HasHomology j']

theorem extendCyclesIso_hom_naturality :
    cyclesMap (extendMap φ e) j' ≫ (L.extendCyclesIso e hj').hom =
      (K.extendCyclesIso e hj').hom ≫ cyclesMap φ j := by
  simp [← cancel_mono (L.iCycles j), extendMap_f φ e hj']

