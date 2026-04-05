import Mathlib

variable {R : Type*} [DivisionRing R] [CharZero R] {p : R}

theorem nsmul_mem_zmultiples_iff_exists_sub_div {r : R} {n : ℕ} (hn : n ≠ 0) :
    n • r ∈ AddSubgroup.zmultiples p ↔
      ∃ k : Fin n, r - (k : ℕ) • (p / n : R) ∈ AddSubgroup.zmultiples p := by
  rw [← natCast_zsmul r, AddSubgroup.zsmul_mem_zmultiples_iff_exists_sub_div (Int.natCast_ne_zero.mpr hn),
    Int.cast_natCast]
  rfl

