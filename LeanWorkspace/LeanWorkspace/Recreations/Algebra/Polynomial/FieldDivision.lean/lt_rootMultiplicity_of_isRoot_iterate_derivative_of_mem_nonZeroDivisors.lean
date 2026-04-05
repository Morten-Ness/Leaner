import Mathlib

open scoped Nat Polynomial

variable {R : Type u} {S : Type v} {k : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [CommRing R]

theorem lt_rootMultiplicity_of_isRoot_iterate_derivative_of_mem_nonZeroDivisors
    {p : R[X]} {t : R} {n : ℕ} (h : p ≠ 0)
    (hroot : ∀ m ≤ n, (derivative^[m] p).IsRoot t)
    (hnzd : (n.factorial : R) ∈ nonZeroDivisors R) :
    n < p.rootMultiplicity t := by
  by_contra! h'
  replace hroot := hroot _ h'
  simp only [IsRoot, Polynomial.eval_iterate_derivative_rootMultiplicity] at hroot
  obtain ⟨q, hq⟩ : ((rootMultiplicity t p)! : R) ∣ n ! := by gcongr
  rw [hq, mul_mem_nonZeroDivisors] at hnzd
  rw [nsmul_eq_mul, mul_left_mem_nonZeroDivisors_eq_zero_iff hnzd.1] at hroot
  exact eval_divByMonic_pow_rootMultiplicity_ne_zero t h hroot

