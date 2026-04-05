import Mathlib

variable {R : Type*} {M : Type u} [Semiring R] [AddCommMonoid M] [Module R M]

theorem spanFinrank_of_not_fg {p : Submodule R M} (hp : ¬p.FG) : p.spanFinrank = 0 := by
  refine toNat_eq_zero.2 ?_
  right
  by_contra! h
  exact hp (Submodule.spanRank_finite_iff_fg.1 h)

