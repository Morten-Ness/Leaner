import Mathlib

variable {α : Type u} {β : Type v}

variable [Monoid α]

theorem mem_conjugatesOf_self {a : α} : a ∈ conjugatesOf a := IsConj.refl _

