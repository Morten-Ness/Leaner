import Mathlib

variable {F M N : Type*}

variable [Monoid M] [Monoid N] {f : F} {x y : M}

theorem irreducible_mul_units (u : Mˣ) : Irreducible (y * u) ↔ Irreducible y := by
  simp only [irreducible_iff, Units.isUnit_mul_units, and_congr_right_iff]
  refine fun _ => ⟨fun h A B HAB => ?_, fun h A B HAB => ?_⟩
  · rw [← u.isUnit_mul_units B]
    apply h
    rw [← mul_assoc, ← HAB]
  · rw [← u⁻¹.isUnit_mul_units B]
    apply h
    rw [← mul_assoc, ← HAB, Units.mul_inv_cancel_right]

