import Mathlib

open scoped DirectSum

variable {ι : Type*} {σ S R : Type*}

variable [DecidableEq ι]

variable [Semiring R] [SetLike σ R] [AddSubmonoidClass σ R] (A : ι → σ)

variable [AddCommMonoid ι] [PartialOrder ι] [CanonicallyOrderedAdd ι] [SetLike.GradedMonoid A]

variable [Sub ι] [OrderedSub ι] [AddLeftReflectLE ι]

theorem coe_mul_of_apply (r : ⨁ i, A i) {i : ι} (r' : A i) (n : ι) [Decidable (i ≤ n)] :
    ((r * of (fun i => A i) i r') n : R) = if i ≤ n then (r (n - i) : R) * r' else 0 := by
  split_ifs with h
  exacts [DirectSum.coe_mul_of_apply_of_le _ _ _ n h, DirectSum.coe_mul_of_apply_of_not_le _ _ _ n h]

