import Mathlib

variable {α ι γ A B C : Type*} [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C]

variable {t : ι → A → C}

variable {s : Finset α} {f : α → ι →₀ A} (i : ι)

variable (g : ι →₀ A) (k : ι → A → γ → B) (x : γ)

variable {β M M' N P G H R S : Type*}

variable [Zero M] [Zero M'] [CommMonoid N]

theorem prod_of_support_subset (f : α →₀ M) {s : Finset α} (hs : f.support ⊆ s) (g : α → M → N)
    (h : ∀ i ∈ s, g i 0 = 1) : f.prod g = ∏ x ∈ s, g x (f x) := by
  refine Finset.prod_subset hs fun x hxs hx => h x hxs ▸ (congr_arg (g x) ?_)
  exact notMem_support_iff.1 hx

