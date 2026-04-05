import Mathlib

variable {α ι γ A B C : Type*} [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C]

variable {t : ι → A → C}

variable {s : Finset α} {f : α → ι →₀ A} (i : ι)

variable (g : ι →₀ A) (k : ι → A → γ → B) (x : γ)

variable {β M M' N P G H R S : Type*}

theorem MonoidHom.finsuppProd_apply [Zero β] [MulOneClass N] [CommMonoid P] (f : α →₀ β)
    (g : α → β → N →* P) (x : N) : f.prod g x = f.prod fun i fi => g i fi x := MonoidHom.finset_prod_apply _ _ _

