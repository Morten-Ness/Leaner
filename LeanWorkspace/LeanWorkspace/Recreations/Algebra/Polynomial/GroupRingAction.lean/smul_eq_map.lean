import Mathlib

open scoped Polynomial

variable (M : Type*) [Monoid M]

variable (R : Type*) [Semiring R]

theorem smul_eq_map [MulSemiringAction M R] (m : M) :
    HSMul.hSMul m = map (MulSemiringAction.toRingHom M R m) := by
  ext
  simp

noncomputable instance [MulSemiringAction M R] : MulSemiringAction M R[X] :=
  { Polynomial.distribMulAction with
    smul_one := fun m ↦
      smul_eq_map R m ▸ Polynomial.map_one (MulSemiringAction.toRingHom M R m)
    smul_mul := fun m _ _ ↦
      smul_eq_map R m ▸ Polynomial.map_mul (MulSemiringAction.toRingHom M R m) }

