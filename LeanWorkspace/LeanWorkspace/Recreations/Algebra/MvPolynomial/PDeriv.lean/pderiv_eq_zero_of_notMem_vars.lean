import Mathlib

variable {R : Type u} {σ : Type v} {a a' a₁ a₂ : R} {s : σ →₀ ℕ}

variable [CommSemiring R]

theorem pderiv_eq_zero_of_notMem_vars {i : σ} {f : MvPolynomial σ R} (h : i ∉ f.vars) :
    MvPolynomial.pderiv i f = 0 := derivation_eq_zero_of_forall_mem_vars fun _ hj => MvPolynomial.pderiv_X_of_ne <| ne_of_mem_of_not_mem hj h

