import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_filter_xor (p q : ι → Prop) [DecidablePred p] [DecidablePred q] :
    (∏ x ∈ s with (Xor' (p x) (q x)), f x) =
      (∏ x ∈ s with (p x ∧ ¬ q x), f x) * (∏ x ∈ s with (q x ∧ ¬ p x), f x) := by
  classical rw [← Finset.prod_union (disjoint_filter_and_not_filter _ _), ← filter_or]
  simp only [Xor']

