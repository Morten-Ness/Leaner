import Mathlib

open scoped DirectSum

variable {ι : Type*} {σ S R : Type*}

variable [DecidableEq ι]

variable [Semiring R] [SetLike σ R] [AddSubmonoidClass σ R] (A : ι → σ)

theorem coe_of_mul_apply_add [AddLeftCancelMonoid ι] [SetLike.GradedMonoid A] {i : ι} (r : A i)
    (r' : ⨁ i, A i) (j : ι) : ((of (fun i => A i) i r * r') (i + j) : R) = r * r' j := DirectSum.coe_of_mul_apply_aux _ _ _ fun _x => ⟨fun h => add_left_cancel h, fun h => h ▸ rfl⟩

