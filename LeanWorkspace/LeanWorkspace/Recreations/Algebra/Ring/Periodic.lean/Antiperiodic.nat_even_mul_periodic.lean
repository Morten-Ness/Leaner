import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Antiperiodic.nat_even_mul_periodic [NonAssocSemiring α] [InvolutiveNeg β]
    (h : Function.Antiperiodic f c) (n : ℕ) : Function.Periodic f (n * (2 * c)) := h.periodic_two_mul.nat_mul n

