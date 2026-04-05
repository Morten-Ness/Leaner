import Mathlib

open scoped Pointwise translate

variable {ι α β M G H : Type*} [AddCommGroup G]

theorem translate_add (a b : G) (f : G → α) : τ (a + b) f = τ a (τ b f) := by ext; simp [sub_sub]

