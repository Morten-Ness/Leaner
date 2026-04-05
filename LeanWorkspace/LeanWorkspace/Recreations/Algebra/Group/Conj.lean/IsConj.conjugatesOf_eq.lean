import Mathlib

variable {α : Type u} {β : Type v}

variable [Monoid α]

theorem IsConj.conjugatesOf_eq {a b : α} (ab : IsConj a b) : conjugatesOf a = conjugatesOf b := Set.ext fun _ => ⟨fun ag => ab.symm.trans ag, fun bg => ab.trans bg⟩

