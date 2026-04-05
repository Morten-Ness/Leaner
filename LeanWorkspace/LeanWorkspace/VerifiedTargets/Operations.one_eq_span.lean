import Mathlib

variable {R : Type u} [Semiring R] {A : Type v} [Semiring A] [Module R A]

theorem one_eq_span : (1 : Submodule R A) = R ∙ 1 := (LinearMap.span_singleton_eq_range _ _ _).symm

