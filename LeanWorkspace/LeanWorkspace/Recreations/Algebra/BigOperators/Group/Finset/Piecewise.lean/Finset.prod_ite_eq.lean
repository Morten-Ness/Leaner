import Mathlib

variable {ι κ M β γ : Type*} {s : Finset ι}

variable [CommMonoid M]

theorem prod_ite_eq [DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M) :
    (∏ x ∈ s, ite (a = x) (b x) 1) = ite (a ∈ s) (b a) 1 := Finset.prod_dite_eq s a fun x _ => b x

