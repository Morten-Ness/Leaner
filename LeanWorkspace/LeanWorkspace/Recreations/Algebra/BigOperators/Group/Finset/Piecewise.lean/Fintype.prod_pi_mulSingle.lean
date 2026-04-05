import Mathlib

variable {ι κ M β γ : Type*} {s : Finset ι}

variable [CommMonoid M] [Fintype ι]

variable [DecidableEq ι]

theorem prod_pi_mulSingle {M : ι → Type*} [∀ i, CommMonoid (M i)] (i : ι) (f : ∀ i, M i) :
    ∏ j, Pi.mulSingle j (f j) i = f i := Fintype.prod_dite_eq _ _

