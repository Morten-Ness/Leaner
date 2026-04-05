import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_union_inter [DecidableEq ι] :
    (∏ x ∈ s₁ ∪ s₂, f x) * ∏ x ∈ s₁ ∩ s₂, f x = (∏ x ∈ s₁, f x) * ∏ x ∈ s₂, f x := fold_union_inter

