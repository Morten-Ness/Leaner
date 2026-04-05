import Mathlib

variable {ι : Type*}

variable {R : Type*}

variable {S : Type*} [SetLike S R] [Monoid R] [AddMonoid ι]

variable {A : ι → S} [SetLike.GradedMonoid A]

theorem pow_mem_graded (n : ℕ) {r : R} {i : ι} (h : r ∈ A i) : r ^ n ∈ A (n • i) := by
  match n with
  | 0 =>
    rw [pow_zero, zero_nsmul]
    exact one_mem_graded _
  | n + 1 =>
    rw [pow_succ', succ_nsmul']
    exact mul_mem_graded h (pow_mem_graded n h)

