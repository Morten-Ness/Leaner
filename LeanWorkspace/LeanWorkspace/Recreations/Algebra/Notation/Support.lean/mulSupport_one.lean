import Mathlib

variable {ι κ M N P : Type*}

variable [One M] [One N] [One P] {f g : ι → M} {s : Set ι} {x : ι}

theorem mulSupport_one : Function.mulSupport (1 : ι → M) = ∅ := Function.mulSupport_eq_empty_iff.2 rfl

