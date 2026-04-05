import Mathlib

variable {R : Type*} [CommSemiring R]

theorem coeff_homogenize (p : R[X]) (n : ℕ) (m : Fin 2 →₀ ℕ) :
    (Polynomial.homogenize p n).coeff m = if m 0 + m 1 = n then coeff p (m 0) else 0 := by
  induction p using Polynomial.induction_on' with
  | add p q ihp ihq =>
    simp [*, ite_add_ite]
  | monomial k c =>
    rcases le_or_gt k n with hkn | hnk
    · rw [Polynomial.homogenize_monomial hkn, coeff_monomial, MvPolynomial.coeff_monomial]
      have : (fun₀ | 0 => m 0 | 1 => m 1) = m := by ext i; fin_cases i <;> simp
      aesop
    · aesop (add simp Polynomial.homogenize_monomial_of_lt) (add simp coeff_monomial)

