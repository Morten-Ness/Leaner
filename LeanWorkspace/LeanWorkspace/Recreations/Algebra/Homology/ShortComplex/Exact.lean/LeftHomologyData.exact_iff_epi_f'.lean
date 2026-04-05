import Mathlib

variable {C D : Type*} [Category* C] [Category* D]

variable [Preadditive C] [Preadditive D] (S : ShortComplex C)

theorem LeftHomologyData.exact_iff_epi_f' [S.HasHomology] (h : LeftHomologyData S) :
    S.Exact ↔ Epi h.f' := by
  constructor
  · intro hS
    exact hS.epi_f' h
  · intro
    simp only [h.exact_iff, IsZero.iff_id_eq_zero, ← cancel_epi h.π, ← cancel_epi h.f',
      comp_id, h.f'_π, comp_zero]

