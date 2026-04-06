FAIL
import Mathlib

variable {R : Type*} [DivisionRing R] [CharZero R] {p : R}

theorem zmultiples_zsmul_eq_zsmul_iff {ψ θ : R ⧸ AddSubgroup.zmultiples p} {z : ℤ} (hz : z ≠ 0) :
    z • ψ = z • θ ↔ ∃ k : Fin z.natAbs, ψ = θ + ((k : ℕ) • (p / z) : R) := by
  classical
  have hpz : ((p / z : R) * z - p) ∈ AddSubgroup.zmultiples p := by
    refine ⟨-1, ?_⟩
    have hzR : (z : R) ≠ 0 := by
      exact_mod_cast hz
    field_simp [div_eq_mul_inv, hzR, mul_comm, mul_left_comm, mul_assoc]
  constructor
  · intro h
    by_cases hp : p = 0
    · subst hp
      refine ⟨0, ?_⟩
      simp
    · have hsub : z • (ψ - θ) = 0 := by
        simpa [zsmul_sub] using sub_eq_zero.mpr h
      rcases QuotientAddGroup.eq_zero_iff.mp hsub with ⟨m, hm⟩
      have hzR : (z : R) ≠ 0 := by
        exact_mod_cast hz
      let kInt : ℤ := m % z
      have hk_nonneg : 0 ≤ kInt := Int.emod_nonneg _ hz
      have hk_lt : kInt < z.natAbs := by
        simpa [kInt] using Int.emod_lt_natAbs m hz
      let k : Fin z.natAbs := ⟨Int.toNat kInt, by
        simpa [Int.toNat_of_nonneg hk_nonneg] using hk_lt⟩
      refine ⟨k, ?_⟩
      apply sub_eq_iff_eq_add.mp
      apply Quotient.sound
      refine ⟨m / z, ?_⟩
      have hdecomp : m = z * (m / z) + kInt := by
        simpa [kInt, add_comm, add_left_comm, add_assoc, mul_comm] using (Int.ediv_add_emod m z).symm
      have hk_cast : ((k : ℕ) : R) = (kInt : R) := by
        simp [k, kInt, Int.toNat_of_nonneg hk_nonneg]
      calc
        ψ - θ - ((k : ℕ) • (p / z) : R)
            = (m : R) • p - ((k : ℕ) • (p / z) : R) := by simpa [hm]
        _ = ((z * (m / z) + kInt : ℤ) : R) * p - ((k : ℕ) : R) * (p / z) := by
              simp [zsmul_eq_mul, nsmul_eq_mul, hdecomp, hk_cast, mul_comm, mul_left_comm, mul_assoc]
        _ = (((z * (m / z) : ℤ) : R) * p + (kInt : R) * p) - ((k : ℕ) : R) * (p / z) := by ring
        _ = (((m / z : ℤ) : R) * z) * p + (kInt : R) * p - ((k : ℕ) : R) * (p / z) := by
              simp [mul_assoc]
        _ = (((m / z : ℤ) : R) : R) * p * z + (kInt : R) * p - ((k : ℕ) : R) * (p / z) := by
              ring
        _ = (((m / z : ℤ) : R) : R) * p * z + ((k : ℕ) : R) * p - ((k : ℕ) : R) * (p / z) := by
              simp [hk_cast]
        _ = (((m / z : ℤ) : R) : R) * p * z + ((k : ℕ) : R) * ((p / z) * z) - ((k : ℕ) : R) * (p / z) := by
              congr 1
              rw [← mul_assoc, div_mul_eq_mul_div, Int.cast_ofNat]
        _ ∈ AddSubgroup.zmultiples p := by
              refine AddSubgroup.add_mem _ ?_ ?_
              · refine ⟨(m / z) * z, ?_⟩
                simp [mul_assoc]
              · have hmem : ((k : ℕ) : R) * ((p / z) * z - p) ∈ AddSubgroup.zmultiples p := by
                  exact AddSubgroup.zsmul_mem _ _ hpz
                simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_assoc] using hmem
    · exfalso
      exact hp (by
        have hsub : z • (ψ - θ) = 0 := by
          simpa [zsmul_sub] using sub_eq_zero.mpr h
        rcases QuotientAddGroup.eq_zero_iff.mp hsub with ⟨m, hm⟩
        have hzR : (z : R) ≠ 0 := by
          exact_mod_cast hz
        by_cases hm0 : m = 0
        · simp [hm0] at hm
        · sorry)
  · rintro ⟨k, hk⟩
    rw [hk]
    have hzR : (z : R) ≠ 0 := by
      exact_mod_cast hz
    calc
      z • (θ + ((k : ℕ) • (p / z) : R)) = z • θ + z • (((k : ℕ) • (p / z) : R) : R ⧸ AddSubgroup.zmultiples p) := by
        rw [zsmul_add]
      _ = z • θ + 0 := by
        have hq : z • (((k : ℕ) • (p / z) : R) : R ⧸ AddSubgroup.zmultiples p) = 0 := by
          apply QuotientAddGroup.eq_zero_iff.mpr
          refine ⟨k, ?_⟩
          simp [zsmul_eq_mul, nsmul_eq_mul, mul_assoc, hzR, div_eq_mul_inv]
        simp [hq]
      _ = z • θ := by simp
