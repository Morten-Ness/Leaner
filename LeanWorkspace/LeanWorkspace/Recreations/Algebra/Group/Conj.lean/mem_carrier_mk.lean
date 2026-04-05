import Mathlib

variable {α : Type u} {β : Type v}

variable [Monoid α]

theorem mem_carrier_mk {a : α} : a ∈ ConjClasses.carrier (ConjClasses.mk a) := IsConj.refl _

