import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem sum_fin [AddCommMonoid S] (f : ℕ → R → S) (hf : ∀ i, f i 0 = 0) {n : ℕ} {p : R[X]}
    (hn : p.degree < n) : (∑ i : Fin n, f i (p.coeff i)) = p.sum f := by
  by_cases hp : p = 0
  · rw [hp, sum_zero_index, Finset.sum_eq_zero]
    intro i _
    exact hf i
  rw [Polynomial.sum_over_range' _ hf n ((natDegree_lt_iff_degree_lt hp).mpr hn),
    Fin.sum_univ_eq_sum_range fun i => f i (p.coeff i)]

