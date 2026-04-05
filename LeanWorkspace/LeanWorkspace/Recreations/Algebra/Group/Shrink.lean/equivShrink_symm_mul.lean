import Mathlib

variable {M α : Type*} [Small.{v} α]

theorem equivShrink_symm_mul [Mul α] (x y : Shrink α) :
    (equivShrink α).symm (x * y) = (equivShrink α).symm x * (equivShrink α).symm y := by
  simp [Equiv.mul_def]

