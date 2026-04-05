import Mathlib

variable {α ι γ A B C : Type*} [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C]

variable {t : ι → A → C}

variable {s : Finset α} {f : α → ι →₀ A} (i : ι)

variable (g : ι →₀ A) (k : ι → A → γ → B) (x : γ)

variable {β M M' N P G H R S : Type*}

variable [Zero M] [Zero M'] [CommMonoid N]

theorem prod_finsetProd_comm {s : Finset β} (f : α →₀ M) (h : α → M → β → N) :
    (f.prod fun a m => ∏ b ∈ s, h a m b) = ∏ b ∈ s, f.prod fun a m => h a m b := Finset.prod_comm

