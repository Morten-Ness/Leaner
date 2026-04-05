import Mathlib

variable {R : Type*} [CommSemiring R]

theorem homogenize_monomial {m n : ℕ} (h : m ≤ n) (r : R) :
    Polynomial.homogenize (monomial m r) n = .monomial (fun₀ | 0 => m | 1 => n - m) r := by
  rw [Polynomial.homogenize, Finset.sum_eq_single (a := (m, n - m))]
  · simp
  · aesop (add simp coeff_monomial)
  · simp [h]

