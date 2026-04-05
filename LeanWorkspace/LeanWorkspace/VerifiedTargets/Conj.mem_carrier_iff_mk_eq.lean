import Mathlib

variable {α : Type u} {β : Type v}

variable [Monoid α]

theorem mem_carrier_iff_mk_eq {a : α} {b : ConjClasses α} :
    a ∈ ConjClasses.carrier b ↔ ConjClasses.mk a = b := by
  revert b
  rw [ConjClasses.forall_isConj]
  intro b
  rw [ConjClasses.carrier, eq_comm, ConjClasses.mk_eq_mk_iff_isConj, ← ConjClasses.quotient_mk_eq_mk, Quotient.lift_mk]
  rfl

