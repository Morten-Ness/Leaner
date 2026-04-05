import Mathlib

variable {F G M N : Type*} [FunLike F M N] [FunLike G N M]

variable [Monoid M] [Monoid N]

theorem unit_inv_map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) :
    (IsUnit.map h f).unit⁻¹ = f ↑h.unit⁻¹ := Units.inv_eq_of_mul_eq_one_left <| by simp [← map_mul]

