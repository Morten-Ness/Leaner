import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Antiperiodic.int_mul_sub_eq [NonAssocRing α] [NonAssocRing β] (h : Function.Antiperiodic f c)
    (n : ℤ) : f (n * c - x) = (n.negOnePow : ℤ) * f (-x) := by
  simpa only [zsmul_eq_mul] using h.zsmul_sub_eq n

