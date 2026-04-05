import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

variable {s : Finset ι} {t : Finset κ} {f : ι → M} {g : κ → M}

variable [DecidableEq κ]

theorem prod_fiberwise_of_maps_to' {g : ι → κ} (h : ∀ i ∈ s, g i ∈ t) (f : κ → M) :
    ∏ j ∈ t, ∏ i ∈ s with g i = j, f j = ∏ i ∈ s, f (g i) := by
  calc
    _ = ∏ j ∈ t, ∏ i ∈ s with g i = j, f (g i) :=
        Finset.prod_congr rfl fun y _ ↦ Finset.prod_congr rfl fun x hx ↦ by rw [(mem_filter.1 hx).2]
    _ = _ := Finset.prod_fiberwise_of_maps_to h _

