import Mathlib

variable {ι κ M β γ : Type*} {s : Finset ι}

variable [CommMonoid M]

theorem prod_pow_boole [DecidableEq ι] (s : Finset ι) (f : ι → M) (a : ι) :
    (∏ x ∈ s, f x ^ ite (a = x) 1 0) = ite (a ∈ s) (f a) 1 := by simp

