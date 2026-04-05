import Mathlib

variable {A M : Type*} [AddCommGroup A] [DivisionCommMonoid M]

theorem map_sub_eq_div (ψ : AddChar A M) (a b : A) : ψ (a - b) = ψ a / ψ b := ψ.toMonoidHom.map_div _ _

