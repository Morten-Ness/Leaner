import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

variable {f g : α → M} {a b : α} {s t : Set α}

theorem finprod_mem_finset_product₃ {γ : Type*} (s : Finset (α × β × γ)) (f : α × β × γ → M) :
    (∏ᶠ (abc) (_ : abc ∈ s), f abc) = ∏ᶠ (a) (b) (c) (_ : (a, b, c) ∈ s), f (a, b, c) := by
  classical
    rw [finprod_mem_finset_product']
    simp_rw [finprod_mem_finset_product']
    simp

