import Mathlib

variable {ι : Sort*} {M : Type*} [Mul M]

theorem unop_injective : (@Subsemigroup.unop M _).Injective := by
  intro S T h
  rw [← Subsemigroup.op_unop S, ← Subsemigroup.op_unop T]
  exact congrArg Subsemigroup.op h
