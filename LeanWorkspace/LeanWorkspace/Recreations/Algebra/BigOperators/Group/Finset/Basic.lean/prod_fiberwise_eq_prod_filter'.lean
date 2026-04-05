import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

variable {s : Finset ι} {t : Finset κ} {f : ι → M} {g : κ → M}

variable [DecidableEq κ]

theorem prod_fiberwise_eq_prod_filter' (s : Finset ι) (t : Finset κ) (g : ι → κ) (f : κ → M) :
    ∏ j ∈ t, ∏ i ∈ s with g i = j, f j = ∏ i ∈ s with g i ∈ t, f (g i) := by
  calc
    _ = ∏ j ∈ t, ∏ i ∈ s with g i = j, f (g i) :=
        Finset.prod_congr rfl fun j _ ↦ Finset.prod_congr rfl fun i hi ↦ by rw [(mem_filter.1 hi).2]
    _ = _ := Finset.prod_fiberwise_eq_prod_filter _ _ _ _

