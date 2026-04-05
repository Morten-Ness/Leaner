import Mathlib

theorem val_isUnit {A M} [AddGroup A] [Monoid M] (φ : AddChar A M) (a : A) : IsUnit (φ a) := IsUnit.map φ.toMonoidHom <| Group.isUnit (Multiplicative.ofAdd a)

