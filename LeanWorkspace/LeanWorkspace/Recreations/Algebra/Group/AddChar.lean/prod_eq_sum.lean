import Mathlib

variable {ι A M : Type*} [AddMonoid A] [CommMonoid M]

theorem prod_eq_sum (s : Finset ι) (ψ : ι → AddChar A M) : ∏ i ∈ s, ψ i = ∑ i ∈ s, ψ i := rfl

