import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable {ι κ ι : Type*} [Fintype ι] [Fintype κ]

variable [CommMonoid M]

theorem prod_of_injective (e : ι → κ) (he : Function.Injective e) (f : ι → M) (g : κ → M)
    (h' : ∀ i ∉ Set.range e, g i = 1) (h : ∀ i, f i = g (e i)) : ∏ i, f i = ∏ j, g j := Finset.prod_of_injOn e he.injOn (by simp) (by simpa using h') (fun i _ ↦ h i)

