import Mathlib

variable {ι : Type*} {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  {c : ComplexShape ι} {K L M K' L' : HomologicalComplex C c}

theorem exactAt_iff_of_quasiIsoAt (f : K ⟶ L) (i : ι)
    [K.HasHomology i] [L.HasHomology i] [QuasiIsoAt f i] :
    K.ExactAt i ↔ L.ExactAt i := ⟨fun hK => (quasiIsoAt_iff_exactAt f i hK).1 inferInstance,
    fun hL => (quasiIsoAt_iff_exactAt' f i hL).1 inferInstance⟩

