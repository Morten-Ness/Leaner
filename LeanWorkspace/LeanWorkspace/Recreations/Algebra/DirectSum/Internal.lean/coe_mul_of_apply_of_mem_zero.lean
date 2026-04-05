import Mathlib

open scoped DirectSum

variable {ι : Type*} {σ S R : Type*}

variable [DecidableEq ι]

variable [Semiring R] [SetLike σ R] [AddSubmonoidClass σ R] (A : ι → σ)

theorem coe_mul_of_apply_of_mem_zero [AddMonoid ι] [SetLike.GradedMonoid A] (r : ⨁ i, A i)
    (r' : A 0) (j : ι) : ((r * of (fun i => A i) 0 r') j : R) = r j * r' := DirectSum.coe_mul_of_apply_aux _ _ _ fun _x => by rw [add_zero]

