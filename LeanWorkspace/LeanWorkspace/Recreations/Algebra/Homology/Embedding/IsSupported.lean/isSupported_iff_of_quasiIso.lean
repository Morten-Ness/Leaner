import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (K L : HomologicalComplex C c') (e' : K ≅ L) (φ : K ⟶ L) (e : c.Embedding c')

theorem isSupported_iff_of_quasiIso [∀ i, K.HasHomology i] [∀ i, L.HasHomology i]
    [QuasiIso φ] :
    K.IsSupported e ↔ L.IsSupported e := by
  simp [isSupported_iff, exactAt_iff_of_quasiIsoAt φ]

