FAIL
import Mathlib

variable {α ι γ A B C : Type*} [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C]

variable {t : ι → A → C}

variable {s : Finset α} {f : α → ι →₀ A} (i : ι)

variable (g : ι →₀ A) (k : ι → A → γ → B) (x : γ)

variable {β M M' N P G H R S : Type*}

theorem prod_add_index' [AddZeroClass M] [CommMonoid N] {f g : α →₀ M} {h : α → M → N}
    (h_zero : ∀ a, h a 0 = 1) (h_add : ∀ a b₁ b₂, h a (b₁ + b₂) = h a b₁ * h a b₂) :
    (f + g).prod h = f.prod h * g.prod h := by
  classical
  rw [Finsupp.prod, Finsupp.prod, Finsupp.prod]
  let s : Finset α := f.support ∪ g.support
  have hsfg : (f + g).support ⊆ s := by
    intro a ha
    rw [Finset.mem_coe, Finset.mem_union, Finsupp.mem_support_iff] at *
    by_cases hf : f a = 0
    · right
      intro hg
      apply ha
      simp [hf, hg]
    · left
      exact hf
  have hsf : f.support ⊆ s := by
    intro a ha
    rw [Finset.mem_coe, Finset.mem_union]
    left
    exact ha
  have hsg : g.support ⊆ s := by
    intro a ha
    rw [Finset.mem_coe, Finset.mem_union]
    right
    exact ha
  rw [Finset.prod_subset hsfg]
  · rw [Finset.prod_subset hsf, Finset.prod_subset hsg]
    · have h1 : ∏ x ∈ s, h x ((f + g) x) = ∏ x ∈ s, (h x (f x) * h x (g x)) := by
        refine Finset.prod_congr rfl ?_
        intro a ha
        simp [h_add]
      rw [h1, Finset.prod_mul_distrib]
    · intro a ha has
      rw [Finsupp.not_mem_support_iff.mp has, h_zero]
    · intro a ha has
      rw [Finsupp.not_mem_support_iff.mp has, h_zero]
  · intro a ha has
    rw [Finsupp.not_mem_support_iff.mp has, h_zero]
