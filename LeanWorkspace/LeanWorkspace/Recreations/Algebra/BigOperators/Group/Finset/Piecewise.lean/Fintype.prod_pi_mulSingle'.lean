import Mathlib

variable {ι κ M β γ : Type*} {s : Finset ι}

variable [CommMonoid M] [Fintype ι]

variable [DecidableEq ι]

theorem prod_pi_mulSingle' (i : ι) (a : M) : ∏ j, Pi.mulSingle i a j = a := Fintype.prod_dite_eq' _ _

