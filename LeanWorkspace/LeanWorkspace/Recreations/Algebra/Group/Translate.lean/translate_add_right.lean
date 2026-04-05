import Mathlib

open scoped Pointwise translate

variable {ι α β M G H : Type*} [AddCommGroup G]

theorem translate_add_right [Add α] (a : G) (f g : G → α) : τ a (f + g) = τ a f + τ a g := rfl

