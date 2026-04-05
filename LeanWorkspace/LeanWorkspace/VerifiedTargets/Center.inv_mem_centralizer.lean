import Mathlib

variable {M : Type*} {S T : Set M}

variable [Group M] {a b : M}

theorem inv_mem_centralizer (ha : a ∈ Set.centralizer S) : a⁻¹ ∈ Set.centralizer S := fun g hg ↦ by rw [mul_inv_eq_iff_eq_mul, mul_assoc, eq_inv_mul_iff_mul_eq, ha g hg]

