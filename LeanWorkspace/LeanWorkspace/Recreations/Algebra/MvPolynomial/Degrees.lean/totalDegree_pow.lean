import Mathlib

variable {R : Type u} {S : Type v}

variable {σ τ : Type*} {r : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] {p q : MvPolynomial σ R}

theorem totalDegree_pow (a : MvPolynomial σ R) (n : ℕ) :
    (a ^ n).totalDegree ≤ n * a.totalDegree := by
  rw [Finset.pow_eq_prod_const, ← Nat.nsmul_eq_mul, Finset.nsmul_eq_sum_const]
  refine supDegree_prod_le rfl (fun _ _ => ?_)
  exact Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)

