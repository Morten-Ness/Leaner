import Mathlib

open scoped Pointwise Ring

variable {R : Type u} {A : Type v}

variable [CommSemiring R] [Ring A] [Algebra R A]

theorem algebraMap_mem_iff (S : Type*) {R A : Type*} [CommSemiring R] [CommSemiring S]
    [Ring A] [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A] {a : A} {r : R} :
    algebraMap R S r ∈ spectrum S a ↔ r ∈ spectrum R a := by
  simp only [spectrum.mem_iff spectrum, Algebra.algebraMap_eq_smul_one, smul_assoc, one_smul]

protected alias ⟨of_algebraMap_mem, algebraMap_mem⟩ := spectrum.algebraMap_mem_iff

