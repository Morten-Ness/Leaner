import Mathlib

variable {R : Type u} {S : Type v}

variable {σ τ : Type*} {r : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] {p q : MvPolynomial σ R}

variable [CommSemiring S]

theorem vars_rename [DecidableEq τ] (f : σ → τ) (φ : MvPolynomial σ R) :
    (rename f φ).vars ⊆ φ.vars.image f := by
  classical
  intro i hi
  simp only [MvPolynomial.vars_def, Multiset.mem_toFinset, Finset.mem_image] at hi ⊢
  simpa only [Multiset.mem_map] using degrees_rename _ _ hi

