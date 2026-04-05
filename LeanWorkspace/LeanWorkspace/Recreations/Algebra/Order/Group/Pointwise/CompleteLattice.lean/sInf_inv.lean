import Mathlib

open scoped Pointwise

variable {M : Type*}

variable [CompleteLattice M]

variable [Group M] [MulLeftMono M] [MulRightMono M]
  (s t : Set M)

theorem sInf_inv (s : Set M) : sInf s⁻¹ = (sSup s)⁻¹ := by
  rw [← image_inv_eq_inv, sInf_image]
  exact ((OrderIso.inv M).map_sSup _).symm

