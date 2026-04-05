import Mathlib

variable {F A B C D : Type*}

variable [Monoid A] [Monoid B] [Star A] [Star B]

theorem coe_ofBijective {f : A →⋆* B} (hf : Function.Bijective f) :
    (StarMulEquiv.ofBijective f hf : A → B) = f := rfl

