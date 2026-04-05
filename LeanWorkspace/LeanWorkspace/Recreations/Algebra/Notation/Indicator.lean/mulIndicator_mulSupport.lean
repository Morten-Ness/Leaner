import Mathlib

variable {α β M N : Type*}

variable [One M] [One N] {s t : Set α} {f g : α → M} {a : α}

theorem mulIndicator_mulSupport : Set.mulIndicator (mulSupport f) f = f := Set.mulIndicator_eq_self.2 Subset.rfl

