import Mathlib

open scoped DirectSum

variable {ι : Type*} {σ S R : Type*}

variable [DecidableEq ι]

variable [Semiring R] [SetLike σ R] [AddSubmonoidClass σ R] (A : ι → σ)

theorem coe_of_mul_apply_of_mem_zero [AddMonoid ι] [SetLike.GradedMonoid A] (r : A 0)
    (r' : ⨁ i, A i) (j : ι) : ((of (fun i => A i) 0 r * r') j : R) = r * r' j := DirectSum.coe_of_mul_apply_aux _ _ _ fun _x => by rw [zero_add]

