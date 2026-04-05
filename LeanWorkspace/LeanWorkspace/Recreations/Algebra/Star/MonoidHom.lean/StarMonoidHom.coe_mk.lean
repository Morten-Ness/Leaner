import Mathlib

variable {F A B C D : Type*}

variable [Monoid A] [Star A] [Monoid B] [Star B]

theorem coe_mk (f : A →* B) (h) : ((⟨f, h⟩ : A →⋆* B) : A → B) = f := rfl

