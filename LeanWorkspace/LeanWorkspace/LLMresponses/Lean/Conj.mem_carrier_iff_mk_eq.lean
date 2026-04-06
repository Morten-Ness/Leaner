FAIL
import Mathlib

variable {α : Type u} {β : Type v}

variable [Monoid α]

theorem mem_carrier_iff_mk_eq {a : α} {b : ConjClasses α} :
    a ∈ ConjClasses.carrier b ↔ ConjClasses.mk a = b := by
  induction b using Quotient.inductionOn with
  | h c =>
      simp [ConjClasses.carrier, ConjClasses.mk]
