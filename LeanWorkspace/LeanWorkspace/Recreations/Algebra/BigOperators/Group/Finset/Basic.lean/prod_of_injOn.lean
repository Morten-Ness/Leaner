import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

variable {s : Finset ι} {t : Finset κ} {f : ι → M} {g : κ → M}

theorem prod_of_injOn (e : ι → κ) (he : Set.InjOn e s) (hest : Set.MapsTo e s t)
    (h' : ∀ i ∈ t, i ∉ e '' s → g i = 1) (h : ∀ i ∈ s, f i = g (e i)) :
    ∏ i ∈ s, f i = ∏ j ∈ t, g j := by
  classical
  exact (prod_nbij e (fun a ↦ mem_image_of_mem e) he (by simp [Set.surjOn_image]) h).trans <|
    Finset.prod_subset (image_subset_iff.2 hest) <| by simpa using h'

