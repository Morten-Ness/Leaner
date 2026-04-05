import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Antiperiodic.nsmul_sub_eq [AddCommGroup α] [SubtractionMonoid β] (h : Function.Antiperiodic f c)
    (n : ℕ) : f (n • c - x) = (-1) ^ n • f (-x) := by
  simpa only [Int.reduceNeg, natCast_zsmul] using h.zsmul_sub_eq n

