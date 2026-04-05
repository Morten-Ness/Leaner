import Mathlib

variable {R : Type*} [CommSemiring R]

theorem homogenize_finsetProd {ι : Type*} {s : Finset ι} {p : ι → R[X]} {n : ι → ℕ}
    (h : ∀ i ∈ s, (p i).natDegree ≤ n i) :
    Polynomial.homogenize (∏ i ∈ s, p i) (∑ i ∈ s, n i) = ∏ i ∈ s, Polynomial.homogenize (p i) (n i) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s hi ihs =>
    simp only [prod_cons, sum_cons, forall_mem_cons] at *
    rw [Polynomial.homogenize_mul _ _ h.1, ihs h.2]
    exact (natDegree_prod_le _ _).trans (Finset.sum_le_sum h.2)

