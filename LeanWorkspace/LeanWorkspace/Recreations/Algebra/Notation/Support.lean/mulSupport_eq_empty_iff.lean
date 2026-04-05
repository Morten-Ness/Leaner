import Mathlib

variable {ι κ M N P : Type*}

variable [One M] [One N] [One P] {f g : ι → M} {s : Set ι} {x : ι}

theorem mulSupport_eq_empty_iff : Function.mulSupport f = ∅ ↔ f = 1 := by
  rw [← subset_empty_iff, Function.mulSupport_subset_iff', funext_iff]
  simp

