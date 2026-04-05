import Mathlib

variable {M α : Type*} [Small.{v} α]

theorem equivShrink_smul {M : Type*} [SMul M α] (m : M) (x : α) :
    equivShrink α (m • x) = m • equivShrink α x := by
  simp [Equiv.smul_def]

