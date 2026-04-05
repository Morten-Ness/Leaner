import Mathlib

variable {α : Type u}

variable {M : Type*}

variable [Monoid M] {a b c : M}

theorem mul_right_inj (h : IsUnit a) : a * b = a * c ↔ b = c := let ⟨u, hu⟩ := h
  hu ▸ Units.mul_right_inj u

