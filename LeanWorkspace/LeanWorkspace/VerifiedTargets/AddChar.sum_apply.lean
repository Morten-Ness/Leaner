import Mathlib

variable {ι A M : Type*} [AddMonoid A] [CommMonoid M]

theorem sum_apply (s : Finset ι) (ψ : ι → AddChar A M) (a : A) :
    (∑ i ∈ s, ψ i) a = ∏ i ∈ s, ψ i a := by rw [AddChar.coe_sum, Finset.prod_apply]

