import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Antiperiodic.int_mul_eq_of_eq_zero [NonAssocRing α] [SubtractionMonoid β]
    (h : Function.Antiperiodic f c) (hi : f 0 = 0) : ∀ n : ℤ, f (n * c) = 0
  | (n : ℕ) => by rw [Int.cast_natCast, h.nat_mul_eq_of_eq_zero hi n]
  | .negSucc n => by rw [Int.cast_negSucc, neg_mul, ← mul_neg, h.neg.nat_mul_eq_of_eq_zero hi]
