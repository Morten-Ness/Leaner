import Mathlib

variable {α ι γ A B C : Type*} [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C]

variable {t : ι → A → C}

variable {s : Finset α} {f : α → ι →₀ A} (i : ι)

variable (g : ι →₀ A) (k : ι → A → γ → B) (x : γ)

variable {β M M' N P G H R S : Type*}

variable [Zero M] [Zero M'] [CommMonoid N]

theorem prod_unique [Unique α] {f : α →₀ M} {g : α → M → N} (h₁ : f default = 0 → g default 0 = 1) :
    f.prod g = g default (f default) := Finsupp.prod_eq_single _ (fun a ↦ by simp [Subsingleton.elim a default]) h₁

