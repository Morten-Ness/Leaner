import Mathlib

variable {R : Type*} {M : Type u} [Semiring R] [AddCommMonoid M] [Module R M]

theorem FG.finite_generators {p : Submodule R M} (hp : p.FG) :
    p.generators.Finite := by
  rw [← Cardinal.lt_aleph0_iff_set_finite, Submodule.generators_card]
  exact Submodule.spanRank_finite_iff_fg.mpr hp

