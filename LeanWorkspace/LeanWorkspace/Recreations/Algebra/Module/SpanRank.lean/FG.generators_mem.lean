import Mathlib

variable {R : Type*} {M : Type u} [Semiring R] [AddCommMonoid M] [Module R M]

theorem FG.generators_mem (p : Submodule R M) : Submodule.generators p ⊆ p := by
  nth_rw 2 [← Submodule.span_generators p]
  exact subset_span (s := Submodule.generators p)

