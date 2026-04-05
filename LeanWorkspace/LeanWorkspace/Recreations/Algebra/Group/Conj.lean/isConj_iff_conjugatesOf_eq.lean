import Mathlib

variable {α : Type u} {β : Type v}

variable [Monoid α]

theorem isConj_iff_conjugatesOf_eq {a b : α} : IsConj a b ↔ conjugatesOf a = conjugatesOf b := ⟨IsConj.conjugatesOf_eq, fun h => by
    have ha := mem_conjugatesOf_self (a := b)
    rwa [← h] at ha⟩

