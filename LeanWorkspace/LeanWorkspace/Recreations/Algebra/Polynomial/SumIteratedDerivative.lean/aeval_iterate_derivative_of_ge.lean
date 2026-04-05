import Mathlib

open scoped Nat

variable {R S : Type*}

variable [CommSemiring R] {A : Type*} [CommRing A] [Algebra R A]

theorem aeval_iterate_derivative_of_ge (p : R[X]) (q : ℕ) {k : ℕ} (hk : q ≤ k) :
    ∃ gp : R[X], gp.natDegree ≤ p.natDegree - k ∧
      ∀ r : A, aeval r (derivative^[k] p) = q ! • aeval r gp := by
  obtain ⟨p', p'_le, hp'⟩ := Polynomial.exists_iterate_derivative_eq_factorial_smul p k
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hk
  refine ⟨((q + k).descFactorial k : R[X]) * p', (natDegree_C_mul_le _ _).trans p'_le, fun r => ?_⟩
  simp_rw [hp', nsmul_eq_mul, map_mul, map_natCast, ← mul_assoc, ← Nat.cast_mul,
    Nat.add_descFactorial_eq_ascFactorial, Nat.factorial_mul_ascFactorial]

