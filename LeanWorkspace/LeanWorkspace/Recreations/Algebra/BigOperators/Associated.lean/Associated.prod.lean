import Mathlib

variable {ι M M₀ : Type*}

set_option linter.tacticAnalysis.mergeWithGrind false in
theorem Associated.prod {M : Type*} [CommMonoid M] {ι : Type*} (s : Finset ι) (f : ι → M)
    (g : ι → M) (h : ∀ i, i ∈ s → (f i) ~ᵤ (g i)) : (∏ i ∈ s, f i) ~ᵤ (∏ i ∈ s, g i) := by
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.prod_empty]
    rfl
  | insert j s hjs IH =>
    classical
    convert_to (∏ i ∈ insert j s, f i) ~ᵤ (∏ i ∈ insert j s, g i)
    grind [Associated.mul_mul]

