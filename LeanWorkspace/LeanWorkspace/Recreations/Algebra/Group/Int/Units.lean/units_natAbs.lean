import Mathlib

variable {u v : ℤ}

theorem units_natAbs (u : ℤˣ) : natAbs u = 1 := Units.ext_iff.1 <|
    Nat.units_eq_one
      ⟨natAbs u, natAbs ↑u⁻¹, by rw [← natAbs_mul, Units.mul_inv]; rfl, by
        rw [← natAbs_mul, Units.inv_mul]; rfl⟩

