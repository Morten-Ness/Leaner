import Mathlib

variable {ι κ M β γ : Type*} {s : Finset ι}

variable [CommMonoid M]

theorem prod_eq_mul_prod_diff_singleton_of_mem [DecidableEq ι] {s : Finset ι} {i : ι} (h : i ∈ s)
    (f : ι → M) : ∏ x ∈ s, f x = f i * ∏ x ∈ s \ {i}, f x := Finset.prod_eq_mul_prod_diff_singleton _ _ (by simp_all)

