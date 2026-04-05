import Mathlib

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

theorem lieCharacter_apply_lie (χ : LieCharacter R L) (x y : L) : χ ⁅x, y⁆ = 0 := by
  rw [LieHom.map_lie, LieRing.of_associative_ring_bracket, mul_comm, sub_self]

