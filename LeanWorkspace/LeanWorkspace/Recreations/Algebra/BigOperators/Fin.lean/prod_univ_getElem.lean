import Mathlib

variable {ι M : Type*}

variable [CommMonoid M] {n : ℕ}

theorem prod_univ_getElem (l : List M) : ∏ i : Fin l.length, l[i.1] = l.prod := by
  simp [Finset.prod_eq_multiset_prod]

