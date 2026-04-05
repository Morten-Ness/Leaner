import Mathlib

variable {ι κ M N P : Type*}

variable [One M] [One N] [One P] {f g : ι → M} {s : Set ι} {x : ι}

theorem mulSupport_nonempty_iff : (Function.mulSupport f).Nonempty ↔ f ≠ 1 := by
  rw [nonempty_iff_ne_empty, Ne, Function.mulSupport_eq_empty_iff]

