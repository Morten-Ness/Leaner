import Mathlib

variable {ι κ M N G α : Type*}

variable {s s₁ s₂ : Finset ι} {a : ι} {f g : ι → M}

variable [CommMonoid M]

theorem ite_one_prod (p : Prop) [Decidable p] (s : Finset ι) (f : ι → M) :
    (if p then 1 else (∏ x ∈ s, f x)) = ∏ x ∈ s, if p then 1 else f x := by
  by_cases hp : p
  · simp [hp]
  · simp [hp]
