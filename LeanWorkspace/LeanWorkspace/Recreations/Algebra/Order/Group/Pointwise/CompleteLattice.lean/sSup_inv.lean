import Mathlib

open scoped Pointwise

variable {M : Type*}

variable [CompleteLattice M]

variable [Group M] [MulLeftMono M] [MulRightMono M]
  (s t : Set M)

theorem sSup_inv (s : Set M) : sSup s⁻¹ = (sInf s)⁻¹ := by
  rw [← image_inv_eq_inv, sSup_image]
  exact ((OrderIso.inv M).map_sInf _).symm

