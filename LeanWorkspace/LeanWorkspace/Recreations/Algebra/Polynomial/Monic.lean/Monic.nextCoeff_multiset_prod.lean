import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {m n : ℕ} {ι : Type y}

variable [CommSemiring R] {p : R[X]}

theorem Monic.nextCoeff_multiset_prod (t : Multiset ι) (f : ι → R[X]) (h : ∀ i ∈ t, Polynomial.Monic (f i)) :
    nextCoeff (t.map f).prod = (t.map fun i => nextCoeff (f i)).sum := by
  revert h
  refine Multiset.induction_on t ?_ fun a t ih ht => ?_
  · simp only [Multiset.notMem_zero, forall_prop_of_true, forall_prop_of_false, Multiset.map_zero,
      Multiset.prod_zero, Multiset.sum_zero, not_false_iff, forall_true_iff]
    rw [← C_1]
    rw [nextCoeff_C_eq_zero]
  · rw [Multiset.map_cons, Multiset.prod_cons, Multiset.map_cons, Multiset.sum_cons,
      Polynomial.Monic.nextCoeff_mul, ih]
    exacts [fun i hi => ht i (Multiset.mem_cons_of_mem hi), ht a (Multiset.mem_cons_self _ _),
      Polynomial.monic_multiset_prod_of_monic _ _ fun b bs => ht _ (Multiset.mem_cons_of_mem bs)]

