import Mathlib

variable {M : Type*}

variable [Monoid M] [Subsingleton Mˣ]

theorem associated_eq_eq : (Associated : M → M → Prop) = Eq := by
  ext
  rw [associated_iff_eq]

