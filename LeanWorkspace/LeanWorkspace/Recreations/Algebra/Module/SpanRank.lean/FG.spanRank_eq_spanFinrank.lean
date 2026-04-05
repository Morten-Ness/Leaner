import Mathlib

variable {R : Type*} {M : Type u} [Semiring R] [AddCommMonoid M] [Module R M]

theorem FG.spanRank_eq_spanFinrank {p : Submodule R M} (fg : p.FG) : p.spanRank = p.spanFinrank := Submodule.fg_iff_spanRank_eq_spanFinrank.mpr fg

