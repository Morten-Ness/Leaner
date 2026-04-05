import Mathlib

variable {σ τ R S : Type*} [CommSemiring R] [CommSemiring S] (p : ℕ)

theorem coe_expand :
    (MvPolynomial.expand p (R := R) (σ := σ)) = eval₂ C ((fun s ↦ X s : σ → MvPolynomial σ R) ^ p) := rfl

