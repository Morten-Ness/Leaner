import Mathlib

variable {R α β : Type*} [Semiring R]

variable (A) [Semiring A] [Module R A] [AddCommMonoid α] [AddCommMonoid β] [Module A β]

theorem LinearEquiv.isScalarTower [Module R α] [Module R β] [IsScalarTower R A β]
    (e : α ≃ₗ[R] β) :
    letI := e.toAddEquiv.module A
    IsScalarTower R A α := by
  letI := e.toAddEquiv.module A
  constructor
  intro x y z
  simp only [Equiv.smul_def, smul_assoc]
  apply e.symm.map_smul

