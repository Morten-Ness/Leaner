import Mathlib

variable {M} [Monoid M] {F} [DivisionRing F]

theorem smul_inv'' [MulSemiringAction M F] (x : M) (m : F) : x • m⁻¹ = (x • m)⁻¹ := map_inv₀ (MulSemiringAction.toRingHom M F x) _

