import Mathlib

variable {R : Type*} {a b : R}

variable [CommRing R]

theorem norm_eq_one_iff_mem_unitary {z : QuadraticAlgebra R a b} :
    z.norm = 1 ↔ z ∈ unitary (QuadraticAlgebra R a b) := by
  rw [Unitary.mem_iff_self_mul_star, ← QuadraticAlgebra.algebraMap_norm_eq_mul_star]
  simp [← algebraMap_inj (R := R) (a := a) (b := b)]

alias ⟨mem_unitary, norm_eq_one⟩ := norm_eq_one_iff_mem_unitary

