import Mathlib

variable {R : Type*} {M : Type u} [Semiring R] [AddCommMonoid M] [Module R M]

theorem fg_iff_spanRank_eq_spanFinrank {p : Submodule R M} : p.spanRank = p.spanFinrank ↔ p.FG := by
  rw [Submodule.spanFinrank, ← Submodule.spanRank_finite_iff_fg, eq_comm]
  exact cast_toNat_eq_iff_lt_aleph0

