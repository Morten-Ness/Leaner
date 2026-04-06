FAIL
import Mathlib

variable {R k V1 P1 V2 P2 V3 P3 : Type*}

variable [CommRing k] [AddCommGroup V1] [AddTorsor V1 P1] [AddCommGroup V2]

variable [Module k V1] [Module k V2]

theorem homothety_injective [Module.IsTorsionFree k V1] [IsCancelMulZero k] (c : P1) {r : k}
    (hr : r ≠ 0) :
    Function.Injective (AffineMap.homothety c r) := by
  intro x y h
  rw [AffineMap.homothety_apply, AffineMap.homothety_apply] at h
  have h' : r • ((x -ᵥ c) - (y -ᵥ c)) = 0 := by
    rw [smul_sub, h, sub_self]
  have h'' : (x -ᵥ c) - (y -ᵥ c) = 0 := by
    exact eq_zero_of_smul_eq_zero_of_ne_zero hr h'
  have h''' : x -ᵥ c = y -ᵥ c := sub_eq_zero.mp h''
  exact vsub_left_cancel h'''
