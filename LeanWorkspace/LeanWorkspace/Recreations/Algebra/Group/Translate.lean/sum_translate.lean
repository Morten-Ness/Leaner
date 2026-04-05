import Mathlib

open scoped Pointwise translate

variable {ι α β M G H : Type*} [AddCommGroup G]

variable [AddCommMonoid M]

theorem sum_translate [Fintype G] (a : G) (f : G → M) : ∑ b, τ a f b = ∑ b, f b := Fintype.sum_equiv (Equiv.subRight _) _ _ fun _ ↦ rfl

