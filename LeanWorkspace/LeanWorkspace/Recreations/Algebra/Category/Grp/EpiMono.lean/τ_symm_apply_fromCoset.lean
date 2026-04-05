import Mathlib

open scoped Pointwise

variable {A B : GrpCat.{u}} (f : A ⟶ B)

theorem τ_symm_apply_fromCoset :
    Equiv.symm τ (fromCoset ⟨f.hom.range, 1, one_leftCoset _⟩) = ∞ := by
  rw [GrpCat.SurjectiveOfEpiAuxs.tau, Equiv.symm_swap, Equiv.swap_apply_left]

