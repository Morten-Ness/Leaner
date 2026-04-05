import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Periodic.int_mul_sub_eq [NonAssocRing α] (h : Function.Periodic f c) (n : ℤ) :
    f (n * c - x) = f (-x) := (h.int_mul _).sub_eq'

