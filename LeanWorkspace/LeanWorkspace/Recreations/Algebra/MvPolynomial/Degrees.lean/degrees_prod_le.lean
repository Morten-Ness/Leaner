import Mathlib

variable {R : Type u} {S : Type v}

variable {σ τ : Type*} {r : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] {p q : MvPolynomial σ R}

theorem degrees_prod_le {ι : Type*} {s : Finset ι} {f : ι → MvPolynomial σ R} :
    (∏ i ∈ s, f i).degrees ≤ ∑ i ∈ s, (f i).degrees := by
  classical exact supDegree_prod_le (map_zero _) (map_add _)

