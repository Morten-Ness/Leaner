import Mathlib

open scoped Pointwise translate

variable {ι α β M G H : Type*} [AddCommGroup G]

theorem translate_translate (a b : G) (f : G → α) : τ a (τ b f) = τ (a + b) f := by
  ext; simp [sub_sub]

