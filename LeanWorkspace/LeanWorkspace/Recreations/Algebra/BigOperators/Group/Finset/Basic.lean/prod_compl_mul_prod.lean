import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_compl_mul_prod [Fintype ι] [DecidableEq ι] (s : Finset ι) (f : ι → M) :
    (∏ i ∈ sᶜ, f i) * ∏ i ∈ s, f i = ∏ i, f i := (@isCompl_compl _ s _).symm.prod_mul_prod f

