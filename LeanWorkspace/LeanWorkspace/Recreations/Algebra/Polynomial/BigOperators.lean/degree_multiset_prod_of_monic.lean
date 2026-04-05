import Mathlib

variable {R : Type u} {ι : Type w}

variable (s : Finset ι)

variable [CommSemiring R] (f : ι → R[X]) (t : Multiset R[X])

theorem degree_multiset_prod_of_monic [Nontrivial R] (h : ∀ f ∈ t, Polynomial.Monic f) :
    t.prod.degree = (t.map degree).sum := by
  have : t.prod ≠ 0 := Polynomial.Monic.ne_zero <| by simpa using monic_multiset_prod_of_monic _ _ h
  rw [degree_eq_natDegree this, Polynomial.natDegree_multiset_prod_of_monic _ h, Nat.cast_multiset_sum,
    Multiset.map_map, Function.comp_def,
    Multiset.map_congr rfl (fun f hf => (degree_eq_natDegree (h f hf).ne_zero).symm)]

