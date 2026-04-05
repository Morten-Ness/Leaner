import Mathlib

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {s : σ →₀ ℕ}

variable (R) [CommSemiring R]

variable (n : ℕ)

theorem degreeOf_coeff_finSuccEquiv (p : MvPolynomial (Fin (n + 1)) R) (j : Fin n) (i : ℕ) :
    degreeOf j (Polynomial.coeff (MvPolynomial.finSuccEquiv R n p) i) ≤ degreeOf j.succ p := by
  rw [degreeOf_eq_sup, degreeOf_eq_sup, Finset.sup_le_iff]
  intro m hm
  rw [← Finsupp.cons_succ j i m]
  exact Finset.le_sup
    (f := fun (g : Fin (Nat.succ n) →₀ ℕ) => g (Fin.succ j))
    (MvPolynomial.mem_support_coeff_finSuccEquiv.1 hm)

