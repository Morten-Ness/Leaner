import Mathlib

variable {n : Type u} [DecidableEq n] [Fintype n] {R : Type v} [CommRing R]

variable {S : Type*} [CommRing S]

theorem map_intCast_injective [CharZero R] :
    Function.Injective ((↑) : Matrix.SpecialLinearGroup n ℤ → Matrix.SpecialLinearGroup n R) := fun g h ↦ by
  simp_rw [Matrix.SpecialLinearGroup.ext_iff, map_apply_coe, RingHom.mapMatrix_apply, Int.coe_castRingHom,
    Matrix.map_apply, Int.cast_inj]
  tauto

