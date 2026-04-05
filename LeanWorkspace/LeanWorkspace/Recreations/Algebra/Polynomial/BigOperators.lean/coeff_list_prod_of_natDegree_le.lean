import Mathlib

open scoped Polynomial

variable {R : Type u} {ι : Type w}

variable (s : Finset ι)

variable {S : Type*} [Semiring S]

theorem coeff_list_prod_of_natDegree_le (l : List S[X]) (n : ℕ) (hl : ∀ p ∈ l, natDegree p ≤ n) :
    coeff (List.prod l) (l.length * n) = (l.map fun p => coeff p n).prod := by
  induction l with
  | nil => simp
  | cons hd tl IH =>
    have hl' : ∀ p ∈ tl, natDegree p ≤ n := fun p hp => hl p (List.mem_cons_of_mem _ hp)
    simp only [List.prod_cons, List.map, List.length]
    rw [add_mul, one_mul, add_comm, ← IH hl', mul_comm tl.length]
    have h : natDegree tl.prod ≤ n * tl.length := by
      refine (Polynomial.natDegree_list_prod_le _).trans ?_
      rw [← tl.length_map natDegree, mul_comm]
      refine List.sum_le_card_nsmul _ _ ?_
      simpa using hl'
    exact coeff_mul_add_eq_of_natDegree_le (hl _ List.mem_cons_self) h

