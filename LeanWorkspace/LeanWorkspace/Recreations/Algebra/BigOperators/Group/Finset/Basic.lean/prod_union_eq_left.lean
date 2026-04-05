import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_union_eq_left [DecidableEq ι] (hs : ∀ a ∈ s₂, a ∉ s₁ → f a = 1) :
    ∏ a ∈ s₁ ∪ s₂, f a = ∏ a ∈ s₁, f a := Eq.symm <|
    Finset.prod_subset subset_union_left fun _a ha ha' ↦ hs _ ((mem_union.1 ha).resolve_left ha') ha'

