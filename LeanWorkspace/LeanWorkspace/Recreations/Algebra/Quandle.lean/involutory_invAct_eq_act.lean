import Mathlib

variable {R : Type*} [Rack R]

theorem involutory_invAct_eq_act {R : Type*} [Rack R] (h : Rack.IsInvolutory R) (x y : R) :
    x ◃⁻¹ y = x ◃ y := by
  rw [← Rack.left_cancel x, right_inv, h x]

