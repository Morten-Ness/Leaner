import Mathlib

variable {R : Type*} {M : Type u} [Semiring R] [AddCommMonoid M] [Module R M]

theorem spanFinrank_span_le_ncard_of_finite {s : Set M} (hs : s.Finite) :
    (span R s).spanFinrank ≤ s.ncard := by
  rw [← Nat.cast_le (α := ℕ∞)]
  exact le_trans (Submodule.spanFinrank_span_le_encard _) hs.cast_ncard_eq.ge

