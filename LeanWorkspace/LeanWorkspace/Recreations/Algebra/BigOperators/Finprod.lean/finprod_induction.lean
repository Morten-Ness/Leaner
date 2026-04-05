import Mathlib

variable {G M N : Type*} {α β ι : Sort*} [CommMonoid M] [CommMonoid N]

theorem finprod_induction {f : α → M} (p : M → Prop) (hp₀ : p 1)
    (hp₁ : ∀ x y, p x → p y → p (x * y)) (hp₂ : ∀ i, p (f i)) : p (∏ᶠ i, f i) := by
  rw [finprod]
  split_ifs
  exacts [Finset.prod_induction _ _ hp₁ hp₀ fun i _ => hp₂ _, hp₀]

