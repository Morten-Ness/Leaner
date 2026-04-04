import Mathlib

variable {k : Type*} {V1 : Type*} {P1 : Type*} {V2 : Type*} {P2 : Type*} {V3 : Type*}
  {P3 : Type*} {V4 : Type*} {P4 : Type*} [Ring k] [AddCommGroup V1] [Module k V1]
  [AddTorsor V1 P1] [AddCommGroup V2] [Module k V2] [AddTorsor V2 P2] [AddCommGroup V3]
  [Module k V3] [AddTorsor V3 P3] [AddCommGroup V4] [Module k V4] [AddTorsor V4 P4]

variable (k P1)

variable {k P1}

variable {P1}

variable {k}

theorem lineMap_eq_lineMap_iff [IsDomain k] [IsTorsionFree k V1] {p₀ p₁ : P1} {c₁ c₂ : k} :
    AffineMap.lineMap p₀ p₁ c₁ = AffineMap.lineMap p₀ p₁ c₂ ↔ p₀ = p₁ ∨ c₁ = c₂ := by
  rw [AffineMap.lineMap_apply, AffineMap.lineMap_apply, ← @vsub_eq_zero_iff_eq V1, vadd_vsub_vadd_cancel_right, ←
    sub_smul, smul_eq_zero, sub_eq_zero, vsub_eq_zero_iff_eq, or_comm, eq_comm]

