import Mathlib

variable {ι : Sort*} {M α : Type*}

theorem smul_inf_le [SMul M α] [SemilatticeInf α] [CovariantClass M α HSMul.hSMul LE.le]
    (m : M) (a₁ a₂ : α) : m • (a₁ ⊓ a₂) ≤ m • a₁ ⊓ m • a₂ := (smul_mono_right _).map_inf_le _ _

