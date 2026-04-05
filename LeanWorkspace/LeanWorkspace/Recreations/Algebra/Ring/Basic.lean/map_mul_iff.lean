import Mathlib

variable {R S : Type*}

variable [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S] {a b : R}

theorem map_mul_iff (f : R →+ S) :
    (∀ x y, f (x * y) = f x * f y) ↔ (AddMonoidHom.mul : R →+ R →+ R).compr₂ f = (AddMonoidHom.mul.comp f).compl₂ f := Iff.symm ext_iff₂

