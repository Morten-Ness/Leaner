import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C]

variable [HasZeroMorphisms C] (K L : HomologicalComplex C c') (φ : K ⟶ L) (e : c.Embedding c')
  [e.IsTruncLE] [∀ i', K.HasHomology i'] [∀ i', L.HasHomology i']

variable [HasZeroObject C]

theorem quasiIso_truncLEMap_iff :
    QuasiIso (truncLEMap φ e) ↔ ∀ (i : ι) (i' : ι') (_ : e.f i = i'), QuasiIsoAt φ i' := by
  rw [← quasiIso_opFunctor_map_iff]
  simp only [← quasiIsoAt_opFunctor_map_iff φ]
  apply quasiIso_truncGEMap_iff

