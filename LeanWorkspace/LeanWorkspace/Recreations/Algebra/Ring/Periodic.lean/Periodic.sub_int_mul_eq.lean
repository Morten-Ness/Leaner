import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Periodic.sub_int_mul_eq [NonAssocRing α] (h : Function.Periodic f c) (n : ℤ) : f (x - n * c) = f x := (h.int_mul n).sub_eq x

