import Mathlib

variable {α : Type u} {β : Type v}

variable [Monoid α]

theorem carrier_eq_preimage_mk {a : ConjClasses α} : a.carrier = ConjClasses.mk ⁻¹' {a} := Set.ext fun _ => ConjClasses.mem_carrier_iff_mk_eq

