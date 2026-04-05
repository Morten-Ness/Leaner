import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Periodic.zsmul [AddGroup α] (h : Function.Periodic f c) (n : ℤ) : Function.Periodic f (n • c) := by
  rcases n with n | n
  · simpa only [Int.ofNat_eq_natCast, natCast_zsmul] using h.nsmul n
  · simpa only [negSucc_zsmul] using (h.nsmul (n + 1)).neg

