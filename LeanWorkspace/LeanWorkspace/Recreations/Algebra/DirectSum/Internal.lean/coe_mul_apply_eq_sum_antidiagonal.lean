import Mathlib

open scoped DirectSum

variable {ι : Type*} {σ S R : Type*}

variable [DecidableEq ι]

variable [Semiring R] [SetLike σ R] [AddSubmonoidClass σ R] (A : ι → σ)

theorem coe_mul_apply_eq_sum_antidiagonal [AddMonoid ι] [HasAntidiagonal ι]
    [SetLike.GradedMonoid A] (r r' : ⨁ i, A i) (n : ι) :
    (r * r') n = ∑ ij ∈ antidiagonal n, (r ij.1 : R) * r' ij.2 := by
  classical
  rw [DirectSum.coe_mul_apply]
  apply Finset.sum_subset (fun _ ↦ by simp)
  aesop (erase simp not_and) (add simp not_and_or)

