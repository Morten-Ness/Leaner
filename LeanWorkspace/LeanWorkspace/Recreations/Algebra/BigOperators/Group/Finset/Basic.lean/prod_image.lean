import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_image [DecidableEq ι] {s : Finset κ} {g : κ → ι} :
    Set.InjOn g s → ∏ x ∈ s.image g, f x = ∏ x ∈ s, f (g x) := fold_image

