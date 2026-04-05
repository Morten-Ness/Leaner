import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

variable {f g : α → M} {a b : α} {s t : Set α}

theorem finprod_mem_induction (p : M → Prop) (hp₀ : p 1) (hp₁ : ∀ x y, p x → p y → p (x * y))
    (hp₂ : ∀ x ∈ s, p <| f x) : p (∏ᶠ i ∈ s, f i) := finprod_induction _ hp₀ hp₁ fun x => finprod_induction _ hp₀ hp₁ <| hp₂ x

