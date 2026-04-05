import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Antiperiodic.nat_mul_sub_eq [NonAssocRing α] [Ring β] (h : Antiperiodic f c) (n : ℕ) :
    f (n * c - x) = (-1) ^ n * f (-x) := by
  simpa only [nsmul_eq_mul, zsmul_eq_mul, Int.cast_pow, Int.cast_neg,
    Int.cast_one] using h.nsmul_sub_eq n

