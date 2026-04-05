import Mathlib

variable {σ : Type*} {τ : Type*} {υ : Type*} {R : Type*} [CommSemiring R]

theorem comap_rename (f : σ → τ) (x : τ → R) : MvPolynomial.comap (rename f) x = x ∘ f := by
  funext
  simp [rename_X, MvPolynomial.comap_apply, aeval_X]

