import Mathlib

open scoped Pointwise translate

variable {ι α β M G H : Type*} [AddCommGroup G]

variable [CommMonoid M]

theorem translate_prod_right (a : G) (f : ι → G → M) (s : Finset ι) :
    τ a (∏ i ∈ s, f i) = ∏ i ∈ s, τ a (f i) := by ext; simp

