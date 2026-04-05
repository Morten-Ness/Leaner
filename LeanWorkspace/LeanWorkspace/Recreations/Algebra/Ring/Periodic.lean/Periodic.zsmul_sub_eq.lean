import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Periodic.zsmul_sub_eq [AddCommGroup α] (h : Function.Periodic f c) (n : ℤ) :
    f (n • c - x) = f (-x) := (h.zsmul _).sub_eq'

