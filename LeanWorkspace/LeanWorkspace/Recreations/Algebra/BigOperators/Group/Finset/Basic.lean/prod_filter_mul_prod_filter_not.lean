import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_filter_mul_prod_filter_not
    (s : Finset ι) (p : ι → Prop) [DecidablePred p] [∀ x, Decidable (¬p x)] (f : ι → M) :
    (∏ x ∈ s with p x, f x) * ∏ x ∈ s with ¬p x, f x = ∏ x ∈ s, f x := by
  have := Classical.decEq ι
  rw [← Finset.prod_union (disjoint_filter_filter_not s s p), filter_union_filter_not_eq]

