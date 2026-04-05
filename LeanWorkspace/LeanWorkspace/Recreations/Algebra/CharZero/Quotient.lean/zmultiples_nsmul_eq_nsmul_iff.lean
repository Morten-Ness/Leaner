import Mathlib

variable {R : Type*} [DivisionRing R] [CharZero R] {p : R}

theorem zmultiples_nsmul_eq_nsmul_iff {ψ θ : R ⧸ AddSubgroup.zmultiples p} {n : ℕ} (hz : n ≠ 0) :
    n • ψ = n • θ ↔ ∃ k : Fin n, ψ = θ + (k : ℕ) • (p / n : R) := by
  rw [← natCast_zsmul ψ, ← natCast_zsmul θ,
    QuotientAddGroup.zmultiples_zsmul_eq_zsmul_iff (Int.natCast_ne_zero.mpr hz), Int.cast_natCast]
  rfl

