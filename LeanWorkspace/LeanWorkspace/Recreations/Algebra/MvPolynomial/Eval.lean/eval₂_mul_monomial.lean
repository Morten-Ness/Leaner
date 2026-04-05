import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

variable (f : R →+* S₁) (g : σ → S₁)

theorem eval₂_mul_monomial :
    ∀ {s a}, (p * monomial s a).eval₂ f g = p.eval₂ f g * f a * s.prod fun n e => g n ^ e := by
  classical
  apply MvPolynomial.induction_on p
  · intro a' s a
    simp [C_mul_monomial, MvPolynomial.eval₂_monomial, f.map_mul]
  · intro p q ih_p ih_q
    simp [add_mul, MvPolynomial.eval₂_add, ih_p, ih_q]
  · intro p n ih s a
    exact
      calc (p * X n * monomial s a).eval₂ f g
        _ = (p * monomial (Finsupp.single n 1 + s) a).eval₂ f g := by
          rw [monomial_single_add, pow_one, mul_assoc]
        _ = (p * monomial (Finsupp.single n 1) 1).eval₂ f g * f a * s.prod fun n e => g n ^ e := by
          simp [ih, prod_single_index, prod_add_index, pow_one, pow_add, mul_assoc, mul_left_comm,
            f.map_one]

