import Mathlib

open scoped Pointwise translate

variable {ι α β M G H : Type*} [AddCommGroup G]

theorem translate_neg_right [Neg α] (a : G) (f : G → α) : τ a (-f) = -τ a f := rfl

