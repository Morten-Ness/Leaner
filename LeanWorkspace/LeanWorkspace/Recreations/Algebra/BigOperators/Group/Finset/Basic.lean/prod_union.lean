import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_union [DecidableEq ι] (h : Disjoint s₁ s₂) :
    ∏ x ∈ s₁ ∪ s₂, f x = (∏ x ∈ s₁, f x) * ∏ x ∈ s₂, f x := by
  rw [← Finset.prod_union_inter, disjoint_iff_inter_eq_empty.mp h]; exact (mul_one _).symm

