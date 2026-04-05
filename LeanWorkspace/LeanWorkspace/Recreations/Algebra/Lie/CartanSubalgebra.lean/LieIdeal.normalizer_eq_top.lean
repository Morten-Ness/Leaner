import Mathlib

variable {R : Type u} {L : Type v}

variable [CommRing R] [LieRing L] [LieAlgebra R L] (H : LieSubalgebra R L)

theorem LieIdeal.normalizer_eq_top {R : Type u} {L : Type v} [CommRing R] [LieRing L]
    [LieAlgebra R L] (I : LieIdeal R L) : (I : LieSubalgebra R L).normalizer = ⊤ := by
  ext x
  simpa only [LieSubalgebra.mem_normalizer_iff, LieSubalgebra.mem_top, iff_true] using
    fun y hy => I.lie_mem hy

