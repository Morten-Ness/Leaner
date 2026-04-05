import Mathlib

variable {R : Type u} {S : Type v}

variable {σ τ : Type*} {r : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] {p q : MvPolynomial σ R}

theorem totalDegree_finset_sum {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ R) :
    (s.sum f).totalDegree ≤ Finset.sup s fun i => (f i).totalDegree := by
  induction s using Finset.cons_induction with
  | empty => exact zero_le _
  | cons a s has hind =>
    rw [Finset.sum_cons, Finset.sup_cons]
    exact (MvPolynomial.totalDegree_add _ _).trans (max_le_max le_rfl hind)

