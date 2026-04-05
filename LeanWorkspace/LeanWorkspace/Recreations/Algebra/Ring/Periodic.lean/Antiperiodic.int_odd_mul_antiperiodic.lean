import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Antiperiodic.int_odd_mul_antiperiodic [NonAssocRing α] [InvolutiveNeg β]
    (h : Function.Antiperiodic f c) (n : ℤ) : Function.Antiperiodic f (n * (2 * c) + c) := fun x => by
  rw [← add_assoc, h, h.int_even_mul_periodic]

