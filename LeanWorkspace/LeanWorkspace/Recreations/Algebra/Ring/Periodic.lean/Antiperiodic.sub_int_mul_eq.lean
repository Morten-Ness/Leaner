import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Antiperiodic.sub_int_mul_eq [NonAssocRing α] [NonAssocRing β] (h : Function.Antiperiodic f c)
    (n : ℤ) : f (x - n * c) = (n.negOnePow : ℤ) * f x := by
  simpa only [zsmul_eq_mul] using h.sub_zsmul_eq n

