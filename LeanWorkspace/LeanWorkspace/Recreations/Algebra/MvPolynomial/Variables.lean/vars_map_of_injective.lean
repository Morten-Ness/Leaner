import Mathlib

variable {R : Type u} {S : Type v}

variable {σ τ : Type*} {r : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] {p q : MvPolynomial σ R}

variable [CommSemiring S] (f : R →+* S)

theorem vars_map_of_injective (hf : Function.Injective f) : (map f p).vars = p.vars := by
  simp [MvPolynomial.vars, degrees_map_of_injective _ hf]

