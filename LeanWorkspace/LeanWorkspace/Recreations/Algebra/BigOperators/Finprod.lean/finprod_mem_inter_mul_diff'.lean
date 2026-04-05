import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

variable {f g : α → M} {a b : α} {s t : Set α}

theorem finprod_mem_inter_mul_diff' (t : Set α) (h : (s ∩ mulSupport f).Finite) :
    ((∏ᶠ i ∈ s ∩ t, f i) * ∏ᶠ i ∈ s \ t, f i) = ∏ᶠ i ∈ s, f i := by
  rw [← finprod_mem_union', inter_union_diff]
  · rw [disjoint_iff_inf_le]
    exact fun x hx => hx.2.2 hx.1.2
  exacts [h.subset fun x hx => ⟨hx.1.1, hx.2⟩, h.subset fun x hx => ⟨hx.1.1, hx.2⟩]

