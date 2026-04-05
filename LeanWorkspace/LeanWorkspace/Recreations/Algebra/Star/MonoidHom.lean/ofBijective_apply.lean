import Mathlib

variable {F A B C D : Type*}

variable [Monoid A] [Monoid B] [Star A] [Star B]

theorem ofBijective_apply {f : A →⋆* B} (hf : Function.Bijective f) (a : A) :
    StarMulEquiv.ofBijective f hf a = f a := rfl

