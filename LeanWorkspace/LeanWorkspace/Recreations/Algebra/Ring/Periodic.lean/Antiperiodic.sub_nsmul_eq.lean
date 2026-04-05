import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Antiperiodic.sub_nsmul_eq [AddGroup α] [SubtractionMonoid β] (h : Function.Antiperiodic f c)
    (n : ℕ) : f (x - n • c) = (-1) ^ n • f x := by
  simpa only [Int.reduceNeg, natCast_zsmul] using h.sub_zsmul_eq n

