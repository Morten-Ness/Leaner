import Mathlib

variable {ι κ M β γ : Type*} {s : Finset ι}

variable [CommMonoid M]

theorem prod_eq_mul_prod_diff_singleton [DecidableEq ι] {s : Finset ι} (i : ι) (f : ι → M)
    (h : i ∉ s → f i = 1) : ∏ x ∈ s, f x = f i * ∏ x ∈ s \ {i}, f x := by
  by_cases hs : i ∈ s
  · convert (Finset.prod_inter_mul_prod_diff s {i} f).symm
    simp [hs]
  · simp_all only [not_false_eq_true, forall_const, one_mul]
    apply Finset.prod_congr <;> aesop

