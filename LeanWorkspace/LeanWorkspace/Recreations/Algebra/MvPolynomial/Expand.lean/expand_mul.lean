import Mathlib

variable {σ τ R S : Type*} [CommSemiring R] [CommSemiring S] (p : ℕ)

theorem expand_mul (q : ℕ) (φ : MvPolynomial σ R) : φ.expand (p * q) = (φ.expand q).expand p := DFunLike.congr_fun (MvPolynomial.expand_mul_eq_comp p q) φ

