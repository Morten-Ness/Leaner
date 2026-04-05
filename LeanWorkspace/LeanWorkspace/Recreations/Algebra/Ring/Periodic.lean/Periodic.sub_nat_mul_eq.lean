import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Periodic.sub_nat_mul_eq [NonAssocRing α] (h : Function.Periodic f c) (n : ℕ) :
    f (x - n * c) = f x := by
  simpa only [nsmul_eq_mul] using h.sub_nsmul_eq n

