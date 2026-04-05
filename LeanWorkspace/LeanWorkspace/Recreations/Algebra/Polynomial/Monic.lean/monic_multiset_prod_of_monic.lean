import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {m n : ℕ} {ι : Type y}

variable [CommSemiring R] {p : R[X]}

theorem monic_multiset_prod_of_monic (t : Multiset ι) (f : ι → R[X]) (ht : ∀ i ∈ t, Polynomial.Monic (f i)) :
    Polynomial.Monic (t.map f).prod := by
  revert ht
  refine t.induction_on ?_ ?_; · simp
  intro a t ih ht
  rw [Multiset.map_cons, Multiset.prod_cons]
  exact (ht _ (Multiset.mem_cons_self _ _)).mul (ih fun _ hi => ht _ (Multiset.mem_cons_of_mem hi))

