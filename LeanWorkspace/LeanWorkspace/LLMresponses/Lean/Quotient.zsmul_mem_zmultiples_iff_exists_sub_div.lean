FAIL
import Mathlib

variable {R : Type*} [DivisionRing R] [CharZero R] {p : R}

theorem zsmul_mem_zmultiples_iff_exists_sub_div {r : R} {z : ℤ} (hz : z ≠ 0) :
    z • r ∈ AddSubgroup.zmultiples p ↔
      ∃ k : Fin z.natAbs, r - (k : ℕ) • (p / z : R) ∈ AddSubgroup.zmultiples p := by
  constructor
  · intro hr
    have hzpos : 0 < z.natAbs := Int.natAbs_pos.mpr hz
    refine ⟨⟨0, hzpos⟩, ?_⟩
    simp only [Fin.coe_mk, Nat.cast_zero, zero_smul, sub_zero]
    exact hr
  · rintro ⟨k, hk⟩
    rcases hk with ⟨m, hm⟩
    refine ⟨m * z + k, ?_⟩
    have hzR : (z : R) ≠ 0 := by
      exact_mod_cast hz
    rw [show ((m * z + k : ℤ) • p : R) = (m * z : ℤ) • p + (k : ℤ) • p by
      simp [add_zsmul]]
    rw [hm]
    have hklt : (k : ℤ) < Int.natAbs z := by
      exact_mod_cast k.2
    have hkmod : ((k : ℤ) : R) = (k : R) := rfl
    calc
      (m * z : ℤ) • p + (k : ℤ) • p
          = z • (m • p) + (k : ℤ) • p := by simp [mul_zsmul]
      _ = z • (r - (k : ℕ) • (p / z : R)) + (k : ℤ) • p := by rw [hm]
      _ = z • r - z • ((k : ℕ) • (p / z : R)) + (k : ℤ) • p := by simp [sub_zsmul]
      _ = z • r - ((k : ℕ) • (z • (p / z : R))) + (k : ℤ) • p := by simp [zsmul_nsmul]
      _ = z • r - (k : ℕ) • p + (k : ℤ) • p := by
        congr 2
        field_simp [div_eq_mul_inv, hzR]
      _ = z • r := by
        norm_num [Int.ofNat_eq_coe, sub_eq_add_neg, add_assoc]
