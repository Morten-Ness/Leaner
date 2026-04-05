import Mathlib

variable {α β : Type*} [CommSemiring α] [PartialOrder α] [Semiring β] [PartialOrder β] [Algebra α β]

variable [ZeroLEOneClass β]

variable [Nontrivial β]

theorem algebraMap_le_algebraMap [SMulPosMono α β] [SMulPosReflectLE α β] {a₁ a₂ : α} :
    algebraMap α β a₁ ≤ algebraMap α β a₂ ↔ a₁ ≤ a₂ := by
  simp [Algebra.algebraMap_eq_smul_one]

