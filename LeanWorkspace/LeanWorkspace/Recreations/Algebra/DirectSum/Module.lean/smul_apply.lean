import Mathlib

open scoped DirectSum

variable {R : Type u} [Semiring R]

variable {ι : Type v}

variable {M : ι → Type w} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

theorem smul_apply (b : R) (v : ⨁ i, M i) (i : ι) : (b • v) i = b • v i := DFinsupp.smul_apply _ _ _

