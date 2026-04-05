import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

theorem finprod_mem_inter_mulSupport_eq (f : α → M) (s t : Set α)
    (h : s ∩ mulSupport f = t ∩ mulSupport f) : ∏ᶠ i ∈ s, f i = ∏ᶠ i ∈ t, f i := by
  rw [← finprod_mem_inter_mulSupport, h, finprod_mem_inter_mulSupport]

