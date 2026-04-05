import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

theorem finprod_mem_eq_prod_of_inter_mulSupport_eq (f : α → M) {s : Set α} {t : Finset α}
    (h : s ∩ mulSupport f = ↑t ∩ mulSupport f) : ∏ᶠ i ∈ s, f i = ∏ i ∈ t, f i := finprod_cond_eq_prod_of_cond_iff _ <| by
    intro x hxf
    rw [← mem_mulSupport] at hxf
    refine ⟨fun hx => ?_, fun hx => ?_⟩
    · refine ((mem_inter_iff x t (mulSupport f)).mp ?_).1
      rw [← Set.ext_iff.mp h x, mem_inter_iff]
      exact ⟨hx, hxf⟩
    · refine ((mem_inter_iff x s (mulSupport f)).mp ?_).1
      rw [Set.ext_iff.mp h x, mem_inter_iff]
      exact ⟨hx, hxf⟩

