import Mathlib

variable {α ι γ A B C : Type*} [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C]

variable {t : ι → A → C}

variable {s : Finset α} {f : α → ι →₀ A} (i : ι)

variable (g : ι →₀ A) (k : ι → A → γ → B) (x : γ)

variable {β M M' N P G H R S : Type*}

theorem prod_sum_index [Zero M] [AddCommMonoid N] [CommMonoid P] {f : α →₀ M}
    {g : α → M → β →₀ N} {h : β → N → P} (h_zero : ∀ a, h a 0 = 1)
    (h_add : ∀ a b₁ b₂, h a (b₁ + b₂) = h a b₁ * h a b₂) :
    (f.sum g).prod h = f.prod fun a b => (g a b).prod h := (Finsupp.prod_finset_sum_index h_zero h_add).symm

