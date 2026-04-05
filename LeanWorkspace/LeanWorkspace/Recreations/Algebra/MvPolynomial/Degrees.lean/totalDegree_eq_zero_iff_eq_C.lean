import Mathlib

variable {R : Type u} {S : Type v}

variable {σ τ : Type*} {r : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] {p q : MvPolynomial σ R}

theorem totalDegree_eq_zero_iff_eq_C {p : MvPolynomial σ R} :
    p.totalDegree = 0 ↔ p = C (p.coeff 0) := by
  constructor <;> intro h
  · ext m; classical rw [coeff_C]; split_ifs with hm; · rw [← hm]
    apply MvPolynomial.coeff_eq_zero_of_totalDegree_lt; rw [h]
    exact Finset.sum_pos (fun i hi ↦ Nat.pos_of_ne_zero <| Finsupp.mem_support_iff.mp hi)
      (Finsupp.support_nonempty_iff.mpr <| Ne.symm hm)
  · rw [h, MvPolynomial.totalDegree_C]

