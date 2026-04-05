import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_union_eq_right [DecidableEq ι] (hs : ∀ a ∈ s₁, a ∉ s₂ → f a = 1) :
    ∏ a ∈ s₁ ∪ s₂, f a = ∏ a ∈ s₂, f a := by rw [union_comm, Finset.prod_union_eq_left hs]

