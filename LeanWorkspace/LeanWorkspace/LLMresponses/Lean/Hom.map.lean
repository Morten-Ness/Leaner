FAIL
import Mathlib

variable {F G M N : Type*} [FunLike F M N] [FunLike G N M]

variable [Monoid M] [Monoid N]

theorem map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : IsUnit (f x) := by
  rcases h with ⟨u, rfl⟩
  refine ⟨
    { val := f u
      inv := f ↑(u⁻¹)
      val_inv := by rw [← map_mul, Units.val_mul, Units.val_inv_eq_one]
      inv_val := by rw [← map_mul, Units.val_mul, Units.inv_mul_eq_one] },
    rfl⟩
