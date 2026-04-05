import Mathlib

variable {R : Type u}

variable [EuclideanDomain R]

theorem zero_div {a : R} : 0 / a = 0 := by _cases (fun a0 : a = 0 => a0.symm ▸ div_zero 0) fun a0 => by
    simpa only [zero_mul] using mul_div_cancel_right₀ 0 a0

