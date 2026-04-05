import Mathlib

variable {α ι γ A B C : Type*} [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C]

variable {t : ι → A → C}

variable {s : Finset α} {f : α → ι →₀ A} (i : ι)

variable (g : ι →₀ A) (k : ι → A → γ → B) (x : γ)

variable {β M M' N P G H R S : Type*}

variable [Zero M] [Zero M'] [CommMonoid N]

theorem prod_zpow {N} [DivisionCommMonoid N] [Fintype α] (f : α →₀ ℤ) (g : α → N) :
    (f.prod fun a b => g a ^ b) = ∏ a, g a ^ f a := Finsupp.prod_fintype f _ fun _ ↦ zpow_zero _

