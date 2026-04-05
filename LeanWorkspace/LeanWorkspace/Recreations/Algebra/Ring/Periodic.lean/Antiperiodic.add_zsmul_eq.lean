import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Antiperiodic.add_zsmul_eq [AddGroup α] [SubtractionMonoid β] (h : Function.Antiperiodic f c)
    (n : ℤ) : f (x + n • c) = (n.negOnePow : ℤ) • f x := by
  rcases Int.even_or_odd' n with ⟨k, rfl | rfl⟩
  · rw [h.even_zsmul_periodic, Int.negOnePow_two_mul, Units.val_one, one_zsmul]
  · rw [h.odd_zsmul_antiperiodic, Int.negOnePow_two_mul_add_one, Units.val_neg,
      Units.val_one, neg_zsmul, one_zsmul]

