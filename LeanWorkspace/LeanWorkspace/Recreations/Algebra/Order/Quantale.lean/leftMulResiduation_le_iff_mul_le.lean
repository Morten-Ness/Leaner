import Mathlib

variable {α : Type*} {ι : Type*} {x y z : α} {s : Set α} {f : ι → α}

variable [Semigroup α] [CompleteLattice α] [IsQuantale α]

theorem leftMulResiduation_le_iff_mul_le : x ≤ y ⇨ₗ z ↔ x * y ≤ z where
  mp h1 := by
    grw [h1]
    simp_all only [Quantale.leftMulResiduation, sSup_mul_distrib, Set.mem_setOf_eq,
      iSup_le_iff, implies_true]
  mpr h1 := le_sSup h1

