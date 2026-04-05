import Mathlib

variable {ι M M₀ : Type*}

variable [CommMonoid M]

theorem prod_eq_one_iff {p : Multiset (Associates M)} :
    p.prod = 1 ↔ ∀ a ∈ p, (a : Associates M) = 1 := Multiset.induction_on p (by simp)
    (by simp +contextual [mul_eq_one, or_imp, forall_and])

