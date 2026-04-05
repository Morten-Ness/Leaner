import Mathlib

variable {R : Type u} {S : Type v}

variable {σ τ : Type*} {r : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] {p q : MvPolynomial σ R}

variable [CommSemiring S] (f : R →+* S)

theorem vars_eq_support_biUnion_support [DecidableEq σ] :
    p.vars = p.support.biUnion Finsupp.support := by
  ext i
  rw [MvPolynomial.mem_vars, Finset.mem_biUnion]

