import Mathlib

variable {R : Type u} {σ : Type v} {a a' a₁ a₂ : R} {s : σ →₀ ℕ}

variable [CommSemiring R]

theorem pderiv_rename {τ : Type*} {f : σ → τ} (hf : Function.Injective f)
    (x : σ) (p : MvPolynomial σ R) :
    MvPolynomial.pderiv (f x) (rename f p) = rename f (MvPolynomial.pderiv x p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p a h =>
    simp only [map_mul, MvPolynomial.rename_X, Derivation.leibniz, MvPolynomial.pderiv_X,
      Pi.single_apply, hf.eq_iff, smul_eq_mul, mul_ite, mul_one, mul_zero, h, map_add]
    split_ifs <;> simp

