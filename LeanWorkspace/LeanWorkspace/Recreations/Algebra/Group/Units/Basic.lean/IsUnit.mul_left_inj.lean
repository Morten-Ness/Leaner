import Mathlib

variable {α : Type u}

variable {M : Type*}

variable [Monoid M] {a b c : M}

theorem mul_left_inj (h : IsUnit a) : b * a = c * a ↔ b = c := let ⟨u, hu⟩ := h
  hu ▸ Units.mul_left_inj u

