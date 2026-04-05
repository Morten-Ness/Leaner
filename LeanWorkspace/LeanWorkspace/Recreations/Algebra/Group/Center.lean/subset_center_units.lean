import Mathlib

variable {M : Type*} {S T : Set M}

variable [Monoid M]

theorem subset_center_units : ((↑) : Mˣ → M) ⁻¹' Set.center M ⊆ Set.center Mˣ := fun _ ha => by
  rw [Set.mem_center_iff _root_.Semigroup]
  intro _
  rw [← Units.val_inj, Units.val_mul, Units.val_mul, ha.comm]

