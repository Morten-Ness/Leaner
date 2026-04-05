import Mathlib

variable {α ι γ A B C : Type*} [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C]

variable {t : ι → A → C}

variable {s : Finset α} {f : α → ι →₀ A} (i : ι)

variable (g : ι →₀ A) (k : ι → A → γ → B) (x : γ)

variable {β M M' N P G H R S : Type*}

theorem MonoidHom.coe_finsuppProd [Zero β] [MulOneClass N] [CommMonoid P] (f : α →₀ β)
    (g : α → β → N →* P) : ⇑(f.prod g) = f.prod fun i fi => ⇑(g i fi) := MonoidHom.coe_finset_prod _ _

