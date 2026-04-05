import Mathlib

open scoped DirectSum

variable {ι : Type*} {σ S R : Type*}

variable [DecidableEq ι]

variable [Semiring R] [SetLike σ R] [AddSubmonoidClass σ R] (A : ι → σ)

set_option backward.isDefEq.respectTransparency false in
theorem coe_mul_apply [AddMonoid ι] [SetLike.GradedMonoid A]
    [∀ (i : ι) (x : A i), Decidable (x ≠ 0)] (r r' : ⨁ i, A i) (n : ι) :
    ((r * r') n : R) =
      ∑ ij ∈ r.support ×ˢ r'.support with ij.1 + ij.2 = n, (r ij.1 * r' ij.2 : R) := by
  rw [mul_eq_sum_support_ghas_mul, DFinsupp.finset_sum_apply, AddSubmonoidClass.coe_finset_sum]
  simp_rw [coe_of_apply, apply_ite, ZeroMemClass.coe_zero, ← Finset.sum_filter, SetLike.coe_gMul]

