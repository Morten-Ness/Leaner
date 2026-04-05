import Mathlib

variable {R : Type u} {S : Type v} {a b : R} {m n : ℕ} {ι : Type y}

variable [CommSemiring R] {p : R[X]}

variable [NoZeroDivisors R] {p q : R[X]}

theorem Monic.not_irreducible_iff_exists_add_mul_eq_coeff (hm : p.Monic) (hnd : p.natDegree = 2) :
    ¬Irreducible p ↔ ∃ c₁ c₂, p.coeff 0 = c₁ * c₂ ∧ p.coeff 1 = c₁ + c₂ := by
  cases subsingleton_or_nontrivial R
  · simp [natDegree_of_subsingleton] at hnd
  rw [hm.irreducible_iff_natDegree', and_iff_right, hnd]
  · push Not
    constructor
    · rintro ⟨a, b, ha, hb, rfl, hdb⟩
      simp only [Nat.Ioc_succ_singleton, zero_add, mem_singleton] at hdb
      have hda := hnd
      rw [Polynomial.Monic.natDegree_mul ha hb, hdb] at hda
      use a.coeff 0, b.coeff 0, mul_coeff_zero a b
      simpa only [nextCoeff, hnd, add_right_cancel hda, hdb] using Polynomial.Monic.nextCoeff_mul ha hb
    · rintro ⟨c₁, c₂, hmul, hadd⟩
      refine
        ⟨Polynomial.X + Polynomial.C c₁, Polynomial.X + Polynomial.C c₂, Polynomial.monic_X_add_C _, Polynomial.monic_X_add_C _, ?_, ?_⟩
      · rw [p.as_sum_range_C_mul_X_pow, hnd, Finset.sum_range_succ, Finset.sum_range_succ,
          Finset.sum_range_one, ← hnd, hm.coeff_natDegree, hnd, hmul, hadd, C_mul, C_add, C_1]
        ring
      · simp
  · rintro rfl
    simp [natDegree_one] at hnd

