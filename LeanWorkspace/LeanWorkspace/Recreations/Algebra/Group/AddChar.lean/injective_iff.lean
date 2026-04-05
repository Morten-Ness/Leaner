import Mathlib

variable {A M : Type*} [AddCommGroup A] [DivisionCommMonoid M]

theorem injective_iff {ψ : AddChar A M} : Function.Injective ψ ↔ ∀ ⦃x⦄, ψ x = 1 → x = 0 := ψ.toMonoidHom.ker_eq_bot_iff.symm.trans eq_bot_iff

