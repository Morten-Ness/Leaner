import Mathlib

variable {α : Type u} {β : Type v}

theorem ofAdd_eq_one {A : Type*} [Zero A] {x : A} : Multiplicative.ofAdd x = 1 ↔ x = 0 := Iff.rfl

