FAIL
import Mathlib

variable {R k V1 P1 V2 P2 V3 P3 : Type*}

variable [CommRing k] [AddCommGroup V1] [AddTorsor V1 P1] [AddCommGroup V2]

variable [Module k V1] [Module k V2]

theorem homothety_eq_iff_of_mul_eq_one {c p q : P1} {r₁ r₂ : k} (h : r₁ * r₂ = 1) :
    AffineMap.homothety c r₁ p = q ↔ AffineMap.homothety c r₂ q = p := by
  constructor
  · intro hpq
    rw [← hpq, AffineMap.homothety_apply, AffineMap.homothety_apply]
    have hmul : r₂ * r₁ = 1 := by rw [mul_comm, h]
    rw [vsub_vadd, smul_smul, hmul, one_smul]
  · intro hqp
    rw [← hqp, AffineMap.homothety_apply, AffineMap.homothety_apply]
    rw [vsub_vadd, smul_smul, h, one_smul]
