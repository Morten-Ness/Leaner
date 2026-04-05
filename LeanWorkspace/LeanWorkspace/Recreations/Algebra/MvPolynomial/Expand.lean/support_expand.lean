import Mathlib

variable {σ τ R S : Type*} [CommSemiring R] [CommSemiring S] (p : ℕ)

variable {p} (φ : MvPolynomial σ R)

theorem support_expand [DecidableEq σ] (hp : p ≠ 0) :
    (MvPolynomial.expand p φ).support = φ.support.image (p • ·) := by
  refine (MvPolynomial.support_expand_subset φ).antisymm ?_
  simp [Finset.image_subset_iff, hp]

