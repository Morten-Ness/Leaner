import Mathlib

open scoped Pointwise translate

variable {ι α β M G H : Type*} [AddCommGroup G]

variable [AddCommMonoid M]

theorem translate_sum_right (a : G) (f : ι → G → M) (s : Finset ι) :
    τ a (∑ i ∈ s, f i) = ∑ i ∈ s, τ a (f i) := by ext; simp

