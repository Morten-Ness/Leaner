import Mathlib

variable {R : Type u} {S : Type v}

variable {σ τ : Type*} {r : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] {p q : MvPolynomial σ R}

variable [LinearOrder σ]

theorem supDegree_toLex_C (r : R) : supDegree toLex (C (σ := σ) r) = 0 := by
  classical
    exact (supDegree_single _ r).trans (ite_eq_iff'.mpr ⟨fun _ => rfl, fun _ => rfl⟩)

