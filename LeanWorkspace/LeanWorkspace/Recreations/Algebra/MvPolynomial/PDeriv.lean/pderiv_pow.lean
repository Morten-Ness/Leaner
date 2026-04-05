import Mathlib

variable {R : Type u} {σ : Type v} {a a' a₁ a₂ : R} {s : σ →₀ ℕ}

variable [CommSemiring R]

theorem pderiv_pow {i : σ} {f : MvPolynomial σ R} {n : ℕ} :
    MvPolynomial.pderiv i (f ^ n) = n * f ^ (n - 1) * MvPolynomial.pderiv i f := by
  rw [(MvPolynomial.pderiv i).leibniz_pow f n, nsmul_eq_mul, smul_eq_mul, mul_assoc]

