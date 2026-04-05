import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Antiperiodic.int_even_mul_periodic [NonAssocRing α] [InvolutiveNeg β] (h : Function.Antiperiodic f c)
    (n : ℤ) : Function.Periodic f (n * (2 * c)) := h.periodic_two_mul.int_mul n

