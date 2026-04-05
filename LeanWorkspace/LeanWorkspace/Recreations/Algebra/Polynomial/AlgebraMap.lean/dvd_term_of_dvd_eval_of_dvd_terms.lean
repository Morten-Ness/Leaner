import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {A' B : Type*} {a b : R} {n : ℕ}

variable [CommSemiring R] [Semiring A] [CommSemiring A'] [Semiring B]

variable [Algebra R A] [Algebra R B]

variable {p q : R[X]} (x : A)

variable [CommRing S] {f : R →+* S}

theorem dvd_term_of_dvd_eval_of_dvd_terms {z p : S} {f : S[X]} (i : ℕ) (dvd_eval : p ∣ f.eval z)
    (dvd_terms : ∀ j ≠ i, p ∣ f.coeff j * z ^ j) : p ∣ f.coeff i * z ^ i := by
  by_cases hi : i ∈ f.support
  · rw [eval, eval₂_eq_sum, sum_def] at dvd_eval
    rw [← Finset.insert_erase hi, Finset.sum_insert (Finset.notMem_erase _ _)] at dvd_eval
    refine (dvd_add_left ?_).mp dvd_eval
    apply Finset.dvd_sum
    intro j hj
    exact dvd_terms j (Finset.ne_of_mem_erase hj)
  · convert dvd_zero p
    rw [notMem_support_iff] at hi
    simp [hi]

