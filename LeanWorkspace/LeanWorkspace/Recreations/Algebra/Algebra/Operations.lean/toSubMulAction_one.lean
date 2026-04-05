import Mathlib

variable {R : Type u} [Semiring R] {A : Type v} [Semiring A] [Module R A]

theorem toSubMulAction_one : (1 : Submodule R A).toSubMulAction = 1 := SetLike.ext fun _ ↦ by rw [Submodule.one_eq_span, SubMulAction.mem_one]; exact mem_span_singleton

