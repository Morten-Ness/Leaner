import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Antiperiodic.nat_odd_mul_antiperiodic [NonAssocSemiring α] [InvolutiveNeg β]
    (h : Function.Antiperiodic f c) (n : ℕ) : Function.Antiperiodic f (n * (2 * c) + c) := fun x => by
  rw [← add_assoc, h, h.nat_even_mul_periodic]

