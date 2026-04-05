import Mathlib

variable {I : Type u}

variable {f : I → Type v}

theorem star_sumElim {I J α : Type*} (x : I → α) (y : J → α) [Star α] :
    star (Sum.elim x y) = Sum.elim (star x) (star y) := by
  ext x; cases x <;> simp only [Pi.star_apply, Sum.elim_inl, Sum.elim_inr]

