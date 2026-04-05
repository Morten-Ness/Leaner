import Mathlib

variable {R : Type*}

variable [Ring R]

theorem splits_neg_iff {f : R[X]} : Polynomial.Splits (-f) ↔ Polynomial.Splits f := ⟨fun hf ↦ neg_neg f ▸ hf.neg, .neg⟩

