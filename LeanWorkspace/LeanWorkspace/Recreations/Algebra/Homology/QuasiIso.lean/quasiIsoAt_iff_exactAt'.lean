import Mathlib

variable {ι : Type*} {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  {c : ComplexShape ι} {K L M K' L' : HomologicalComplex C c}

theorem quasiIsoAt_iff_exactAt' (f : K ⟶ L) (i : ι) [K.HasHomology i] [L.HasHomology i]
    (hL : L.ExactAt i) :
    QuasiIsoAt f i ↔ K.ExactAt i := by
  simp only [quasiIsoAt_iff, ShortComplex.quasiIso_iff, exactAt_iff,
    ShortComplex.exact_iff_isZero_homology] at hL ⊢
  constructor
  · intro h
    exact IsZero.of_iso hL (@asIso _ _ _ _ _ h)
  · intro hK
    exact ⟨⟨0, IsZero.eq_of_src hK _ _, IsZero.eq_of_tgt hL _ _⟩⟩

