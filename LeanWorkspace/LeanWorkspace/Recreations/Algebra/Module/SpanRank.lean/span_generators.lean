import Mathlib

variable {R : Type*} {M : Type u} [Semiring R] [AddCommMonoid M] [Module R M]

theorem span_generators (p : Submodule R M) : span R (Submodule.generators p) = p := (Classical.choose_spec (Submodule.exists_span_set_card_eq_spanRank p)).2

