import Mathlib

variable {α ι γ A B C : Type*} [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C]

variable {t : ι → A → C}

variable {s : Finset α} {f : α → ι →₀ A} (i : ι)

variable (g : ι →₀ A) (k : ι → A → γ → B) (x : γ)

variable {β M M' N P G H R S : Type*}

theorem prod_add_index [DecidableEq α] [AddZeroClass M] [CommMonoid N] {f g : α →₀ M}
    {h : α → M → N} (h_zero : ∀ a ∈ f.support ∪ g.support, h a 0 = 1)
    (h_add : ∀ a ∈ f.support ∪ g.support, ∀ (b₁ b₂), h a (b₁ + b₂) = h a b₁ * h a b₂) :
    (f + g).prod h = f.prod h * g.prod h := by
  rw [Finsupp.prod_of_support_subset f subset_union_left h h_zero,
    Finsupp.prod_of_support_subset g subset_union_right h h_zero, ←
    Finset.prod_mul_distrib, Finsupp.prod_of_support_subset (f + g) Finsupp.support_add h h_zero]
  exact Finset.prod_congr rfl fun x hx => by apply h_add x hx

