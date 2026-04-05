import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Periodic.sub_zsmul_eq [AddGroup α] (h : Function.Periodic f c) (n : ℤ) : f (x - n • c) = f x := (h.zsmul n).sub_eq x

