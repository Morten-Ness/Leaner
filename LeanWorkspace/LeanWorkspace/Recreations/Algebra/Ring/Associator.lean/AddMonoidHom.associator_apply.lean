import Mathlib

variable {R : Type*}

variable [NonUnitalNonAssocRing R] (a b c : R)

theorem associator_apply : AddMonoidHom.associator a b c = _root_.associator a b c := rfl

