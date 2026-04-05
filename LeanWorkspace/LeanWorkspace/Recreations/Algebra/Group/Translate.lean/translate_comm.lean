import Mathlib

open scoped Pointwise translate

variable {ι α β M G H : Type*} [AddCommGroup G]

theorem translate_comm (a b : G) (f : G → α) : τ a (τ b f) = τ b (τ a f) := by
  rw [← translate_add, translate_add']

-- We make `simp` push the `τ` outside

