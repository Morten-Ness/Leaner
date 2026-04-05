import Mathlib

variable {α ι γ A B C : Type*} [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C]

variable {t : ι → A → C}

variable {s : Finset α} {f : α → ι →₀ A} (i : ι)

variable (g : ι →₀ A) (k : ι → A → γ → B) (x : γ)

variable {β M M' N P G H R S : Type*}

theorem prod_attach_index [CommMonoid N] {s : Finset α} (f : α → M) {h : α → M → N} :
    ∏ x ∈ s.attach, h x (f x) = ∏ x ∈ s, h x (f x) := prod_attach _ fun x ↦ h x (f x)

