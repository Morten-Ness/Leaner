import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

variable {f g : α → M} {a b : α} {s t : Set α}

theorem finprod_prod_filter [DecidableEq α] (f : β → α) (s : Finset β) (g : β → M) :
    ∏ᶠ x, ∏ y ∈ s with f y = x, g y = ∏ k ∈ s, g k := by
  rw [finprod_eq_finset_prod_of_mulSupport_subset]
  · rw [Finset.prod_image']
    exact fun _ _ ↦ rfl
  · intro x hx
    rw [mem_mulSupport] at hx
    obtain ⟨a, h, -⟩ := Finset.exists_ne_one_of_prod_ne_one hx
    simp only [Finset.mem_filter, Finset.coe_image, mem_image, SetLike.mem_coe] at h ⊢
    exact ⟨a, h⟩

