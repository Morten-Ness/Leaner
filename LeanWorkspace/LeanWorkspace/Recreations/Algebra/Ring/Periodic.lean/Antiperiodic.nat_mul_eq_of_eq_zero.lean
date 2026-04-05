import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Antiperiodic.nat_mul_eq_of_eq_zero [NonAssocSemiring α] [NegZeroClass β]
    (h : Function.Antiperiodic f c) (hi : f 0 = 0) : ∀ n : ℕ, f (n * c) = 0
  | 0 => by rwa [Nat.cast_zero, zero_mul]
  | n + 1 => by simp [add_mul, h _, Function.Antiperiodic.nat_mul_eq_of_eq_zero h hi n]
