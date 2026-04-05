import Mathlib

variable {ι M : Type*}

variable [CommMonoid M] {n : ℕ}

theorem prod_univ_fun_getElem (l : List ι) (f : ι → M) :
    ∏ i : Fin l.length, f l[i.1] = (l.map f).prod := by
  simp [Finset.prod_eq_multiset_prod]

