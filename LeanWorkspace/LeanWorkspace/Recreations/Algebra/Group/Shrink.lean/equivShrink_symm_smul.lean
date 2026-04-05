import Mathlib

variable {M α : Type*} [Small.{v} α]

theorem equivShrink_symm_smul {M : Type*} [SMul M α] (m : M) (x : Shrink α) :
    (equivShrink α).symm (m • x) = m • (equivShrink α).symm x := by
  simp [Equiv.smul_def]

