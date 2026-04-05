import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_congr_of_eq_on_inter {ι M : Type*} {s₁ s₂ : Finset ι} {f g : ι → M} [CommMonoid M]
    (h₁ : ∀ a ∈ s₁, a ∉ s₂ → f a = 1) (h₂ : ∀ a ∈ s₂, a ∉ s₁ → g a = 1)
    (h : ∀ a ∈ s₁, a ∈ s₂ → f a = g a) :
    ∏ a ∈ s₁, f a = ∏ a ∈ s₂, g a := by
  classical
  conv_lhs => rw [← sdiff_union_inter s₁ s₂, Finset.prod_union_eq_right (by simp_all)]
  conv_rhs => rw [← sdiff_union_inter s₂ s₁, Finset.prod_union_eq_right (by simp_all), inter_comm]
  exact Finset.prod_congr rfl (by simpa)

