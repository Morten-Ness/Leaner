import Mathlib

variable {ι F M N O G H : Type*}

variable [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid O]

theorem mapRange.addMonoidHom_toZeroHom (f : M →+ N) :
    (Finsupp.mapRange.addMonoidHom f).toZeroHom = Finsupp.mapRange.zeroHom (ι := ι) f.toZeroHom := rfl

