import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Antiperiodic.add_nat_mul_eq [NonAssocSemiring α] [Ring β] (h : Antiperiodic f c) (n : ℕ) :
    f (x + n * c) = (-1) ^ n * f x := by
  simpa only [nsmul_eq_mul, zsmul_eq_mul, Int.cast_pow, Int.cast_neg,
    Int.cast_one] using h.add_nsmul_eq n

