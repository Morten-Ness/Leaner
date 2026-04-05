import Mathlib

variable {ι F M N O G H : Type*}

variable [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid O]

theorem mapRange.addMonoidHom_id :
    Finsupp.mapRange.addMonoidHom (AddMonoidHom.id M) = AddMonoidHom.id (ι →₀ M) := AddMonoidHom.ext mapRange_id

