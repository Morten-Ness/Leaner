import Mathlib

variable {F A B C D : Type*}

variable [Monoid A] [Star A] [Monoid B] [Star B]

variable [Monoid C] [Star C] [Monoid D] [Star D]

theorem coe_comp (f : B →⋆* C) (g : A →⋆* B) : ⇑(StarMonoidHom.comp f g) = f ∘ g := rfl

