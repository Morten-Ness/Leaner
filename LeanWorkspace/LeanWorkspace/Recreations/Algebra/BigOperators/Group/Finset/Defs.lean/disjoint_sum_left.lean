import Mathlib

variable {ι κ M N G α : Type*}

variable {s s₁ s₂ : Finset ι} {a : ι} {f g : ι → M}

theorem disjoint_sum_left {a : Multiset α} {i : Multiset (Multiset α)} :
    Disjoint i.sum a ↔ ∀ b ∈ i, Disjoint b a := Quotient.inductionOn i fun l => by
    rw [quot_mk_to_coe, Multiset.sum_coe]
    exact Multiset.disjoint_list_sum_left

