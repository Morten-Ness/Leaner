import Mathlib

open scoped DirectSum

variable {ι : Type*} {σ S R : Type*}

variable [DecidableEq ι]

variable [Semiring R] [SetLike σ R] [AddSubmonoidClass σ R] (A : ι → σ)

theorem coe_mul_of_apply_add [AddRightCancelMonoid ι] [SetLike.GradedMonoid A] (r : ⨁ i, A i)
    {i : ι} (r' : A i) (j : ι) : ((r * of (fun i => A i) i r') (j + i) : R) = r j * r' := DirectSum.coe_mul_of_apply_aux _ _ _ fun _x => ⟨fun h => add_right_cancel h, fun h => h ▸ rfl⟩

