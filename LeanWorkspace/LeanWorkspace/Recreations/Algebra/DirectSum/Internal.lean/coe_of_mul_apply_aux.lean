import Mathlib

open scoped DirectSum

variable {ι : Type*} {σ S R : Type*}

variable [DecidableEq ι]

variable [Semiring R] [SetLike σ R] [AddSubmonoidClass σ R] (A : ι → σ)

theorem coe_of_mul_apply_aux [AddMonoid ι] [SetLike.GradedMonoid A] {i : ι} (r : A i)
    (r' : ⨁ i, A i) {j n : ι} (H : ∀ x : ι, i + x = n ↔ x = j) :
    ((of (fun i => A i) i r * r') n : R) = r * r' j := by
  classical
    rw [DirectSum.coe_mul_apply_eq_dfinsuppSum]
    apply (DFinsupp.sum_single_index _).trans
    swap
    · simp_rw [ZeroMemClass.coe_zero, zero_mul, ite_self]
      exact DFinsupp.sum_zero
    simp_rw [DFinsupp.sum, H, Finset.sum_ite_eq']
    split_ifs with h
    · rfl
    rw [DFinsupp.notMem_support_iff.mp h, ZeroMemClass.coe_zero, mul_zero]

