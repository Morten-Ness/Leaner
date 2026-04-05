import Mathlib

variable {ι : Type*} {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  {c : ComplexShape ι} {K L M K' L' : HomologicalComplex C c}

theorem quasiIso_iff (f : K ⟶ L) [∀ i, K.HasHomology i] [∀ i, L.HasHomology i] :
    QuasiIso f ↔ ∀ i, QuasiIsoAt f i := ⟨fun h => h.quasiIsoAt, fun h => ⟨h⟩⟩

attribute [instance] QuasiIso.quasiIsoAt

