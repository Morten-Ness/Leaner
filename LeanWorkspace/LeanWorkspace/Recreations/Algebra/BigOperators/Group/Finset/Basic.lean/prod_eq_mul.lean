import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_eq_mul {s : Finset ι} {f : ι → M} (a b : ι) (hn : a ≠ b)
    (h₀ : ∀ c ∈ s, c ≠ a ∧ c ≠ b → f c = 1) (ha : a ∉ s → f a = 1) (hb : b ∉ s → f b = 1) :
    ∏ x ∈ s, f x = f a * f b := by
  haveI := Classical.decEq ι; by_cases h₁ : a ∈ s <;> by_cases h₂ : b ∈ s
  · exact Finset.prod_eq_mul_of_mem a b h₁ h₂ hn h₀
  · rw [hb h₂, mul_one]
    apply Finset.prod_eq_single_of_mem a h₁
    exact fun c hc hca => h₀ c hc ⟨hca, ne_of_mem_of_not_mem hc h₂⟩
  · rw [ha h₁, one_mul]
    apply Finset.prod_eq_single_of_mem b h₂
    exact fun c hc hcb => h₀ c hc ⟨ne_of_mem_of_not_mem hc h₁, hcb⟩
  · rw [ha h₁, hb h₂, mul_one]
    exact
      _root_.trans
        (Finset.prod_congr rfl fun c hc =>
          h₀ c hc ⟨ne_of_mem_of_not_mem hc h₁, ne_of_mem_of_not_mem hc h₂⟩)
        prod_const_one

