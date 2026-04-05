import Mathlib

variable {R : Type u} [Semiring R] {A : Type v} [Semiring A] [Module R A]

theorem one_eq_span_one_set : (1 : Submodule R A) = span R 1 := Submodule.one_eq_span

