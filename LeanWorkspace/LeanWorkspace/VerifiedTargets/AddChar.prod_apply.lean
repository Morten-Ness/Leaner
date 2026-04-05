import Mathlib

variable {ι A M : Type*} [AddMonoid A] [CommMonoid M]

theorem prod_apply (s : Finset ι) (ψ : ι → AddChar A M) (a : A) :
    (∏ i ∈ s, ψ i) a = ∏ i ∈ s, ψ i a := by rw [AddChar.coe_prod, Finset.prod_apply]

