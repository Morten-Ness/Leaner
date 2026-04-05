import Mathlib

variable {α : Type u}

variable {M : Type*} {N : Type*}

theorem Units.isUnit_mul_units [Monoid M] (a : M) (u : Mˣ) : IsUnit (a * u) ↔ IsUnit a := Iff.intro
    (fun ⟨v, hv⟩ => by
      have : IsUnit (a * ↑u * ↑u⁻¹) := by exists v * u⁻¹; rw [← hv, Units.val_mul]
      rwa [mul_assoc, Units.mul_inv, mul_one] at this)
    fun v => v.mul u.isUnit

