import Mathlib

open scoped DirectSum

variable {ι : Type*} {σ S R : Type*}

variable [DecidableEq ι]

variable [Semiring R] [SetLike σ R] [AddSubmonoidClass σ R] (A : ι → σ)

variable [AddCommMonoid ι] [PartialOrder ι] [CanonicallyOrderedAdd ι] [SetLike.GradedMonoid A]

variable [Sub ι] [OrderedSub ι] [AddLeftReflectLE ι]

theorem coe_of_mul_apply {i : ι} (r : A i) (r' : ⨁ i, A i) (n : ι) [Decidable (i ≤ n)] :
    ((of (fun i => A i) i r * r') n : R) = if i ≤ n then (r * r' (n - i) : R) else 0 := by
  split_ifs with h
  exacts [DirectSum.coe_of_mul_apply_of_le _ _ _ n h, DirectSum.coe_of_mul_apply_of_not_le _ _ _ n h]

