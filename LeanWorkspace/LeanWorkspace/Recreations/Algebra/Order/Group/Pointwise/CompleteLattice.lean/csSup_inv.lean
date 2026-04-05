import Mathlib

open scoped Pointwise

variable {M : Type*}

variable [ConditionallyCompleteLattice M]

variable [Group M] [MulLeftMono M] [MulRightMono M]
  {s t : Set M}

theorem csSup_inv (hs₀ : s.Nonempty) (hs₁ : BddBelow s) : sSup s⁻¹ = (sInf s)⁻¹ := by
  rw [← image_inv_eq_inv]
  exact ((OrderIso.inv _).map_csInf' hs₀ hs₁).symm

