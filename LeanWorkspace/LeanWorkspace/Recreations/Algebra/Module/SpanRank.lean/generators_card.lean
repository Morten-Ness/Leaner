import Mathlib

variable {R : Type*} {M : Type u} [Semiring R] [AddCommMonoid M] [Module R M]

theorem generators_card (p : Submodule R M) : #(Submodule.generators p) = Submodule.spanRank p := (Classical.choose_spec (Submodule.exists_span_set_card_eq_spanRank p)).1

