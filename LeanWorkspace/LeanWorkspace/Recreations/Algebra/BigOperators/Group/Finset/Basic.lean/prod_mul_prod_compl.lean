import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_mul_prod_compl [Fintype ι] [DecidableEq ι] (s : Finset ι) (f : ι → M) :
    (∏ i ∈ s, f i) * ∏ i ∈ sᶜ, f i = ∏ i, f i := IsCompl.prod_mul_prod isCompl_compl f

