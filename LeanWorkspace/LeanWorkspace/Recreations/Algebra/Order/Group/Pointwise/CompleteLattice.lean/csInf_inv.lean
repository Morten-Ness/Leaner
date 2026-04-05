import Mathlib

open scoped Pointwise

variable {M : Type*}

variable [ConditionallyCompleteLattice M]

variable [Group M] [MulLeftMono M] [MulRightMono M]
  {s t : Set M}

theorem csInf_inv (hs₀ : s.Nonempty) (hs₁ : BddAbove s) : sInf s⁻¹ = (sSup s)⁻¹ := by
  rw [← image_inv_eq_inv]
  exact ((OrderIso.inv _).map_csSup' hs₀ hs₁).symm

