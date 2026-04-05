import Mathlib

variable {ι κ M N G α : Type*}

variable {s s₁ s₂ : Finset ι} {a : ι} {f g : ι → M}

variable [CommMonoid M]

theorem prod_ite_irrel (p : Prop) [Decidable p] (s : Finset ι) (f g : ι → M) :
    ∏ x ∈ s, (if p then f x else g x) = if p then ∏ x ∈ s, f x else ∏ x ∈ s, g x := by
  split_ifs with h <;> rfl

