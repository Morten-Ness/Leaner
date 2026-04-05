import Mathlib

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {R S σ τ : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]

theorem MvPolynomial.eval_comp_toMvPolynomial (f : σ → R) (i : σ) :
    (eval f).comp (toMvPolynomial (R := R) i) = Polynomial.evalRingHom (f i) := by
  ext <;> simp

