import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Periodic.zsmul_eq [AddGroup α] (h : Function.Periodic f c) (n : ℤ) : f (n • c) = f 0 := (h.zsmul n).eq

