import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_disjSum (s : Finset ι) (t : Finset κ) (f : ι ⊕ κ → M) :
    ∏ x ∈ s.disjSum t, f x = (∏ x ∈ s, f (Sum.inl x)) * ∏ x ∈ t, f (Sum.inr x) := by
  rw [← map_inl_disjUnion_map_inr, Finset.prod_disjUnion, prod_map, prod_map]
  rfl

