import Mathlib

variable {A M : Type*} [AddCommGroup A] [CommMonoid M]

theorem div_apply (ψ χ : AddChar A M) (a : A) : (ψ / χ) a = ψ a * χ (-a) := rfl

