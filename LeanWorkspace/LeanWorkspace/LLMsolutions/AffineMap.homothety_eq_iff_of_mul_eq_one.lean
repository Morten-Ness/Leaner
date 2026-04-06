FAIL
import Mathlib

variable {R k V1 P1 V2 P2 V3 P3 : Type*}

variable [CommRing k] [AddCommGroup V1] [AddTorsor V1 P1] [AddCommGroup V2]

variable [Module k V1] [Module k V2]

theorem homothety_eq_iff_of_mul_eq_one {c p q : P1} {r₁ r₂ : k} (h : r₁ * r₂ = 1) :
    AffineMap.homothety c r₁ p = q ↔ AffineMap.homothety c r₂ q = p := by
  constructor
  · intro hpq
    rw [← hpq]
    rw [AffineMap.homothety_apply, AffineMap.homothety_apply]
    calc
      r₂ • (r₁ • (p -ᵥ c)) +ᵥ c = (r₂ * r₁) • (p -ᵥ c) +ᵥ c := by rw [smul_smul]
      _ = (1 : k) • (p -ᵥ c) +ᵥ c := by simpa [mul_comm] using congrArg (fun t => t • (p -ᵥ c) +ᵥ c) h
      _ = p := by simp
  · intro hqp
    rw [← hqp]
    rw [AffineMap.homothety_apply, AffineMap.homothety_apply]
    calc
      r₁ • (r₂ • (q -ᵥ c)) +ᵥ c = (r₁ * r₂) • (q -ᵥ c) +ᵥ c := by rw [smul_smul]
      _ = (1 : k) • (q -ᵥ c) +ᵥ c := by simpa using congrArg (fun t => t • (q -ᵥ c) +ᵥ c) h
      _ = q := by simp
