import Mathlib

variable {α ι γ A B C : Type*} [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C]

variable {t : ι → A → C}

variable {s : Finset α} {f : α → ι →₀ A} (i : ι)

variable (g : ι →₀ A) (k : ι → A → γ → B) (x : γ)

variable {β M M' N P G H R S : Type*}

theorem sum_apply [Zero M] [AddCommMonoid N] {f : α →₀ M} {g : α → M → β →₀ N} {a₂ : β} :
    (f.sum g) a₂ = f.sum fun a₁ b => g a₁ b a₂ := Finsupp.finset_sum_apply _ _ _

