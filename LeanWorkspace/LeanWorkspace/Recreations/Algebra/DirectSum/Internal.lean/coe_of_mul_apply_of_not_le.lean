import Mathlib

open scoped DirectSum

variable {ι : Type*} {σ S R : Type*}

variable [DecidableEq ι]

variable [Semiring R] [SetLike σ R] [AddSubmonoidClass σ R] (A : ι → σ)

variable [AddCommMonoid ι] [PartialOrder ι] [CanonicallyOrderedAdd ι] [SetLike.GradedMonoid A]

theorem coe_of_mul_apply_of_not_le {i : ι} (r : A i) (r' : ⨁ i, A i) (n : ι) (h : ¬i ≤ n) :
    ((of (fun i => A i) i r * r') n : R) = 0 := by
  classical
    rw [DirectSum.coe_mul_apply_eq_dfinsuppSum]
    apply (DFinsupp.sum_single_index _).trans
    swap
    · simp_rw [ZeroMemClass.coe_zero, zero_mul, ite_self]
      exact DFinsupp.sum_zero
    · rw [DFinsupp.sum, Finset.sum_ite_of_false, Finset.sum_const_zero]
      exact fun x _ H => h ((self_le_add_right i x).trans_eq H)

