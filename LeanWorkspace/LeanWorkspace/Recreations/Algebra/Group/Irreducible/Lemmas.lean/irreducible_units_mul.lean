import Mathlib

variable {F M N : Type*}

variable [Monoid M] [Monoid N] {f : F} {x y : M}

theorem irreducible_units_mul (u : Mˣ) : Irreducible (u * y) ↔ Irreducible y := by
  simp only [irreducible_iff, Units.isUnit_units_mul, and_congr_right_iff]
  refine fun _ => ⟨fun h A B HAB => ?_, fun h A B HAB => ?_⟩
  · rw [← u.isUnit_units_mul]
    apply h
    rw [mul_assoc, ← HAB]
  · rw [← u⁻¹.isUnit_units_mul]
    apply h
    rw [mul_assoc, ← HAB, Units.inv_mul_cancel_left]

