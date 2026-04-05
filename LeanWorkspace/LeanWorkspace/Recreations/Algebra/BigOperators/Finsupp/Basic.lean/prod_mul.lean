import Mathlib

variable {α ι γ A B C : Type*} [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C]

variable {t : ι → A → C}

variable {s : Finset α} {f : α → ι →₀ A} (i : ι)

variable (g : ι →₀ A) (k : ι → A → γ → B) (x : γ)

variable {β M M' N P G H R S : Type*}

theorem prod_mul [Zero M] [CommMonoid N] {f : α →₀ M} {h₁ h₂ : α → M → N} :
    (f.prod fun a b => h₁ a b * h₂ a b) = f.prod h₁ * f.prod h₂ := Finset.prod_mul_distrib

