import Mathlib

variable {R : Type*} [Rack R]

theorem ad_conj {R : Type*} [Rack R] (x y : R) : Rack.act' (x ◃ y) = Rack.act' x * Rack.act' y * (Rack.act' x)⁻¹ := by
  rw [eq_mul_inv_iff_mul_eq]; ext z
  apply self_distrib.symm

