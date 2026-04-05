import Mathlib

variable {R : Type u} {S : Type v}

variable {σ τ : Type*} {r : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] {p q : MvPolynomial σ R}

theorem degrees_map_le [CommSemiring S] {f : R →+* S} : (map f p).degrees ≤ p.degrees := by
  classical exact Finset.sup_mono <| support_map_subset ..

