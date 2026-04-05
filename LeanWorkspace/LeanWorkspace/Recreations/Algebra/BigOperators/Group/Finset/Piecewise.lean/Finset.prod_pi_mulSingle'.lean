import Mathlib

variable {ι κ M β γ : Type*} {s : Finset ι}

variable [CommMonoid M]

theorem prod_pi_mulSingle' [DecidableEq ι] (a : ι) (x : M) (s : Finset ι) :
    ∏ a' ∈ s, Pi.mulSingle a x a' = if a ∈ s then x else 1 := Finset.prod_dite_eq' _ _ _

