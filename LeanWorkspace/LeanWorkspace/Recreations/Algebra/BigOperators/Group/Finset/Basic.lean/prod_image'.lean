import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_image' [DecidableEq ι] {s : Finset κ} {g : κ → ι} (h : κ → M)
    (eq : ∀ i ∈ s, f (g i) = ∏ j ∈ s with g j = g i, h j) :
    ∏ a ∈ s.image g, f a = ∏ i ∈ s, h i := calc
    ∏ a ∈ s.image g, f a = ∏ a ∈ s.image g, ∏ j ∈ s with g j = a, h j :=
      (Finset.prod_congr rfl) fun _a hx =>
        let ⟨i, his, hi⟩ := mem_image.1 hx
        hi ▸ eq i his
    _ = ∏ i ∈ s, h i := Finset.prod_fiberwise_of_maps_to (fun _ => mem_image_of_mem g) _

