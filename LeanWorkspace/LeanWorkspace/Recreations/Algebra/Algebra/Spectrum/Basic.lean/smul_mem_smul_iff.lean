import Mathlib

open scoped Pointwise Ring

variable {R : Type u} {A : Type v}

variable [CommSemiring R] [Ring A] [Algebra R A]

theorem smul_mem_smul_iff {a : A} {s : R} {r : Rˣ} : r • s ∈ σ (r • a) ↔ s ∈ σ a := by
  simp only [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one, smul_assoc, ← smul_sub, isUnit_smul_iff]

