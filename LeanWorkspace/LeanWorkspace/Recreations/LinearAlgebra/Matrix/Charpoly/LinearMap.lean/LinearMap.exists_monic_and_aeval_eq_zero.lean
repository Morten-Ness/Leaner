import Mathlib

open scoped Polynomial

variable {ι : Type*} [Fintype ι]

variable {M : Type*} [AddCommGroup M] (R : Type*) [CommRing R] [Module R M] (I : Ideal R)

variable (b : ι → M)

theorem LinearMap.exists_monic_and_aeval_eq_zero [Module.Finite R M] (f : Module.End R M) :
    ∃ p : R[X], p.Monic ∧ Polynomial.aeval f p = 0 := (LinearMap.exists_monic_and_coeff_mem_pow_and_aeval_eq_zero_of_range_le_smul R f ⊤ (by simp)).imp
    fun _ h => h.imp_right And.right

