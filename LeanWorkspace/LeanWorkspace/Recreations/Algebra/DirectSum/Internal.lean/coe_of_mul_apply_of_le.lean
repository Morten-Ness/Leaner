import Mathlib

open scoped DirectSum

variable {ι : Type*} {σ S R : Type*}

variable [DecidableEq ι]

variable [Semiring R] [SetLike σ R] [AddSubmonoidClass σ R] (A : ι → σ)

variable [AddCommMonoid ι] [PartialOrder ι] [CanonicallyOrderedAdd ι] [SetLike.GradedMonoid A]

variable [Sub ι] [OrderedSub ι] [AddLeftReflectLE ι]

theorem coe_of_mul_apply_of_le {i : ι} (r : A i) (r' : ⨁ i, A i) (n : ι) (h : i ≤ n) :
    ((of (fun i => A i) i r * r') n : R) = r * r' (n - i) := DirectSum.coe_of_mul_apply_aux _ _ _ fun x => by rw [eq_tsub_iff_add_eq_of_le h, add_comm]

