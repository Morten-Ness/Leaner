import Mathlib

variable (R : Type*)

variable [AddGroupWithOne R] (p : ℕ) [CharP R p] {a b : ℤ}

theorem intCast_injOn_Ico [IsRightCancelAdd R] : InjOn (Int.cast : ℤ → R) (Ico 0 p) := by
  rintro a ⟨ha₀, ha⟩ b ⟨hb₀, hb⟩ hab
  lift a to ℕ using ha₀
  lift b to ℕ using hb₀
  norm_cast at *
  exact CharP.natCast_injOn_Iio _ _ ha hb hab

