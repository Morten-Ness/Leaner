import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_comp [DecidableEq κ] (f : κ → M) (g : ι → κ) :
    ∏ a ∈ s, f (g a) = ∏ b ∈ s.image g, f b ^ #{a ∈ s | g a = b} := by
  simp_rw [← Finset.prod_const, Finset.prod_fiberwise_of_maps_to' fun _ ↦ mem_image_of_mem _]

