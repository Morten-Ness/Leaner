import Mathlib

variable {ι : Type*} {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  {c : ComplexShape ι} {K L M K' L' : HomologicalComplex C c}

theorem quasiIsoAt_of_retract {f : K ⟶ L} {f' : K' ⟶ L'}
    (h : RetractArrow f f') (i : ι) [K.HasHomology i] [L.HasHomology i]
    [K'.HasHomology i] [L'.HasHomology i] [hf' : QuasiIsoAt f' i] :
    QuasiIsoAt f i := by
  rw [quasiIsoAt_iff] at hf' ⊢
  exact ShortComplex.quasiIso_of_retract (h.map (shortComplexFunctor C c i))

