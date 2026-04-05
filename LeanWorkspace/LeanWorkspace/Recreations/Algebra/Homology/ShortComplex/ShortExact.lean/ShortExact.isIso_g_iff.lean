import Mathlib

variable {C D : Type*} [Category* C] [Category* D]

variable [Preadditive C]

theorem ShortExact.isIso_g_iff {S : CategoryTheory.ShortComplex C} (hS : S.ShortExact) [Balanced C] :
    IsIso S.g ↔ IsZero S.X₁ := by
  have := hS.exact.hasZeroObject
  have := hS.mono_f
  have := hS.epi_g
  constructor
  · intro hf
    simp only [IsZero.iff_id_eq_zero, ← cancel_mono S.f, ← cancel_mono S.g,
      S.zero, zero_comp, assoc, comp_zero]
  · intro hX₁
    have : Mono S.g := (S.exact_iff_mono (hX₁.eq_of_src _ _)).1 hS.exact
    apply isIso_of_mono_of_epi

