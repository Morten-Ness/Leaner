import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Antiperiodic.sub_zsmul_eq [AddGroup α] [SubtractionMonoid β] (h : Function.Antiperiodic f c)
    (n : ℤ) : f (x - n • c) = (n.negOnePow : ℤ) • f x := by
  simpa only [sub_eq_add_neg, neg_zsmul, Int.negOnePow_neg] using h.add_zsmul_eq (-n)

