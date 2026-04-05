import Mathlib

variable {α β : Type*} [CommSemiring α] [PartialOrder α] [Semiring β] [PartialOrder β] [Algebra α β]

variable [ZeroLEOneClass β]

variable [Nontrivial β]

variable (β) [SMulPosStrictMono α β]

theorem algebraMap_lt_algebraMap [SMulPosReflectLT α β] {a₁ a₂ : α} :
    algebraMap α β a₁ < algebraMap α β a₂ ↔ a₁ < a₂ := by
  simp [Algebra.algebraMap_eq_smul_one]

