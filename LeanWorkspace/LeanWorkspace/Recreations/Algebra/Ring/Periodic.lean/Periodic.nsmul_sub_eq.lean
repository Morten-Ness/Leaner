import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Periodic.nsmul_sub_eq [SubtractionCommMonoid α] (h : Function.Periodic f c) (n : ℕ) :
    f (n • c - x) = f (-x) := (h.nsmul n).sub_eq'

