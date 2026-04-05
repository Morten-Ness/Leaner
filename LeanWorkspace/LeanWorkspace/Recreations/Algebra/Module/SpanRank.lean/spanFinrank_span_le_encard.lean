import Mathlib

variable {R : Type*} {M : Type u} [Semiring R] [AddCommMonoid M] [Module R M]

theorem spanFinrank_span_le_encard (s : Set M) : (span R s).spanFinrank ≤ s.encard := by
  rw [Submodule.spanFinrank, Set.encard, ENat.card]
  exact le_trans (by simp) (toENat.monotone' (Submodule.spanRank_span_le_card (R := R) s))

