import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

variable (s : Subsemiring R)

theorem multiset_prod_mem {R} [CommSemiring R] (s : Subsemiring R) (m : Multiset R) :
    (∀ a ∈ m, a ∈ s) → m.prod ∈ s := multiset_prod_mem m

