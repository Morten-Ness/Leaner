import Mathlib

open scoped DirectSum

variable {R : Type u} {ι : Type v} [CommRing R]

variable {L : Type w₁} {M : ι → Type w}

variable [LieRing L] [LieAlgebra R L]

variable [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

variable [∀ i, LieRingModule L (M i)] [∀ i, LieModule R L (M i)]

theorem lie_module_bracket_apply (x : L) (m : ⨁ i, M i) (i : ι) : ⁅x, m⁆ i = ⁅x, m i⁆ := mapRange_apply _ _ m i

