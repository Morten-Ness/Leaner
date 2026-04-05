FAIL
import Mathlib

variable {R k V1 P1 V2 P2 V3 P3 : Type*}

variable [CommRing k] [AddCommGroup V1] [AddTorsor V1 P1] [AddCommGroup V2]

variable [Module k V1] [Module k V2]

theorem homothety_injective [Module.IsTorsionFree k V1] [IsCancelMulZero k] (c : P1) {r : k}
    (hr : r ≠ 0) :
    Function.Injective (AffineMap.homothety c r) := by
  intro x y hxy
  rw [AffineMap.homothety_apply, AffineMap.homothety_apply] at hxy
  have hsub : r • (x -ᵥ c) = r • (y -ᵥ c) := by
    simpa using congrArg (fun p : P1 => p -ᵥ c) hxy
  have hvsub : x -ᵥ c = y -ᵥ c := by
    exact Module.IsTorsionFree.smul_left_cancel_of_nonzero hr hsub
  exact (eq_vsub_iff_vsub_eq.mp rfl).mp hvsub
