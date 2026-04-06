import Mathlib

variable {ι κ M N G α : Type*}

variable {s s₁ s₂ : Finset ι} {a : ι} {f g : ι → M}

variable [CommMonoid M]

theorem ite_prod_one (p : Prop) [Decidable p] (s : Finset ι) (f : ι → M) :
    (if p then (∏ x ∈ s, f x) else 1) = ∏ x ∈ s, if p then f x else 1 := by
  by_cases hp : p
  · simp [hp]
  · simp [hp]
