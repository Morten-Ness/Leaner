import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

variable (s : Subsemiring R)

theorem multiset_sum_mem (m : Multiset R) : (∀ a ∈ m, a ∈ s) → m.sum ∈ s := multiset_sum_mem m

