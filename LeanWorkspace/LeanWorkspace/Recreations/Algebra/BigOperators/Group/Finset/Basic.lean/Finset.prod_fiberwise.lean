import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

variable {s : Finset ι} {t : Finset κ} {f : ι → M} {g : κ → M}

variable [DecidableEq κ]

variable [Fintype κ]

theorem prod_fiberwise (s : Finset ι) (g : ι → κ) (f : ι → M) :
    ∏ j, ∏ i ∈ s with g i = j, f i = ∏ i ∈ s, f i := Finset.prod_fiberwise_of_maps_to (fun _ _ ↦ mem_univ _) _

