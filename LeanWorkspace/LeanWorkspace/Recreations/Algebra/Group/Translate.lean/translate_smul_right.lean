import Mathlib

open scoped Pointwise translate

variable {ι α β M G H : Type*} [AddCommGroup G]

theorem translate_smul_right [SMul H α] (a : G) (f : G → α) (c : H) : τ a (c • f) = c • τ a f := rfl

