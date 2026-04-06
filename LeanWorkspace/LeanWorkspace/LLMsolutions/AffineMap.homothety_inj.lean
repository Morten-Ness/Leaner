FAIL
import Mathlib

variable {R k V1 P1 V2 P2 V3 P3 : Type*}

variable [CommRing k] [AddCommGroup V1] [AddTorsor V1 P1] [AddCommGroup V2]

variable [Module k V1] [Module k V2]

theorem homothety_inj [Module.IsTorsionFree k V1] [IsCancelMulZero k] (c : P1) {r : k} (hr : r ≠ 0)
    {p q : P1} :
    AffineMap.homothety c r p = AffineMap.homothety c r q ↔ p = q := by
  constructor
  · intro h
    have hv : r • (p -ᵥ c) = r • (q -ᵥ c) := by
      have h' := congrArg (fun x => x -ᵥ c) h
      simpa [AffineMap.homothety_apply] using h'
    have hzero : r • ((p -ᵥ c) - (q -ᵥ c)) = 0 := by
      rw [smul_sub, hv, sub_self]
    have hsub : (p -ᵥ c) - (q -ᵥ c) = 0 := by
      exact eq_of_smul_eq_smul_of_ne_zero hr (by simpa using hzero)
    have hvc : p -ᵥ c = q -ᵥ c := sub_eq_zero.mp hsub
    exact vsub_left_cancel hvc
  · intro h
    simp [h]
