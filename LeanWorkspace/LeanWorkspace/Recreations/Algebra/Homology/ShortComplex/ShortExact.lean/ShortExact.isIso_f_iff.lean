import Mathlib

variable {C D : Type*} [Category* C] [Category* D]

variable [Preadditive C]

theorem ShortExact.isIso_f_iff {S : CategoryTheory.ShortComplex C} (hS : S.ShortExact) [Balanced C] :
    IsIso S.f ↔ IsZero S.X₃ := by
  have := hS.exact.hasZeroObject
  have := hS.mono_f
  have := hS.epi_g
  constructor
  · intro hf
    simp only [IsZero.iff_id_eq_zero, ← cancel_epi S.g, ← cancel_epi S.f,
      S.zero_assoc, zero_comp]
  · intro hX₃
    have : Epi S.f := (S.exact_iff_epi (hX₃.eq_of_tgt _ _)).1 hS.exact
    apply isIso_of_mono_of_epi

