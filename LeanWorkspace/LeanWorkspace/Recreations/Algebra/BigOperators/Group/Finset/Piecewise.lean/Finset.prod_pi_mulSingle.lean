import Mathlib

variable {ι κ M β γ : Type*} {s : Finset ι}

variable [CommMonoid M]

theorem prod_pi_mulSingle {M : ι → Type*} [DecidableEq ι] [∀ a, CommMonoid (M a)] (a : ι)
    (f : ∀ a, M a) (s : Finset ι) :
    (∏ a' ∈ s, Pi.mulSingle a' (f a') a) = if a ∈ s then f a else 1 := Finset.prod_dite_eq _ _ _

