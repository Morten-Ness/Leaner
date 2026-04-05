import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Antiperiodic.sub_eq [AddGroup α] [InvolutiveNeg β] (h : Function.Antiperiodic f c) (x : α) :
    f (x - c) = -f x := by simp only [← neg_eq_iff_eq_neg, ← h (x - c), sub_add_cancel]

