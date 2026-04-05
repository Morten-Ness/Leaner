import Mathlib

variable {R : Type*}

variable [CommSemiring R]

theorem Splits.multisetProd {m : Multiset R[X]} (hm : ∀ f ∈ m, Polynomial.Splits f) : Polynomial.Splits m.prod := multiset_prod_mem _ hm

