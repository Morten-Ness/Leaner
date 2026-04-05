import Mathlib

variable {R : Type u} {σ : Type v} {a a' a₁ a₂ : R} {s : σ →₀ ℕ}

variable [CommSemiring R]

theorem aeval_sumElim_pderiv_inl {S τ : Type*} [CommRing S] [Algebra R S]
    (p : MvPolynomial (σ ⊕ τ) R) (f : τ → S) (j : σ) :
    aeval (Sum.elim X (C ∘ f)) ((MvPolynomial.pderiv (Sum.inl j)) p) =
      (MvPolynomial.pderiv j) ((aeval (Sum.elim X (C ∘ f))) p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p q h =>
    simp only [Derivation.leibniz, MvPolynomial.pderiv_X, smul_eq_mul, map_add, map_mul, aeval_X, h]
    cases q <;> simp [Pi.single_apply]

