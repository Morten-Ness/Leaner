import Mathlib

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {s : σ →₀ ℕ}

variable (R) [CommSemiring R]

variable (n : ℕ)

theorem finSuccEquiv_apply (p : MvPolynomial (Fin (n + 1)) R) :
    MvPolynomial.finSuccEquiv R n p =
      eval₂Hom (Polynomial.C.comp (Polynomial.C : R →+* MvPolynomial (Fin n) R))
        (fun i : Fin (n + 1) => Fin.cases Polynomial.X (fun k => Polynomial.C (Polynomial.X k)) i) p := by
  rw [← MvPolynomial.finSuccEquiv_eq, RingHom.coe_coe]

