import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Antiperiodic.periodic_two_mul [NonAssocSemiring α] [InvolutiveNeg β]
    (h : Function.Antiperiodic f c) : Function.Periodic f (2 * c) := nsmul_eq_mul 2 c ▸ h.periodic

