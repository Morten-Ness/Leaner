import Mathlib

variable {α : Type*} {ι : Type*} {x y z : α} {s : Set α} {f : ι → α}

variable [Semigroup α] [CompleteLattice α] [IsQuantale α]

theorem rightMulResiduation_le_iff_mul_le : x ≤ y ⇨ᵣ z ↔ y * x ≤ z where
  mp h1 := by
    grw [h1]
    simp_all only [Quantale.rightMulResiduation, mul_sSup_distrib, Set.mem_setOf_eq,
      iSup_le_iff, implies_true]
  mpr h1 := le_sSup h1

