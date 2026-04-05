import Mathlib

variable {ι : Type*} {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  {c : ComplexShape ι} {K L M K' L' : HomologicalComplex C c}

theorem quasiIsoAt_iff_exactAt (f : K ⟶ L) (i : ι) [K.HasHomology i] [L.HasHomology i]
    (hK : K.ExactAt i) :
    QuasiIsoAt f i ↔ L.ExactAt i := by
  simp only [quasiIsoAt_iff, ShortComplex.quasiIso_iff, exactAt_iff,
    ShortComplex.exact_iff_isZero_homology] at hK ⊢
  constructor
  · intro h
    exact IsZero.of_iso hK (@asIso _ _ _ _ _ h).symm
  · intro hL
    exact ⟨⟨0, IsZero.eq_of_src hK _ _, IsZero.eq_of_tgt hL _ _⟩⟩

