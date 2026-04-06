FAIL
import Mathlib

variable {G : Type*} [AddCommGroup G] {p a a₁ a₂ b b₁ b₂ c : G} {n : ℕ} {z : ℤ}

theorem modEq_zero_iff_eq_zsmul : a ≡ 0 [PMOD p] ↔ ∃ z : ℤ, a = z • p := by
  constructor
  · intro h
    rcases h with ⟨n, hn⟩
    refine ⟨- (n : ℤ), ?_⟩
    have := congrArg (fun x => x + (-(n : ℤ)) • p) hn
    simpa [add_assoc, add_comm, add_left_comm, sub_eq_add_neg, zsmul_natCast] using this
  · rintro ⟨z, rfl⟩
    by_cases hz : 0 ≤ z
    · refine ⟨Int.toNat z, ?_⟩
      rw [Int.toNat_of_nonneg hz]
      simp [zsmul_natCast, add_comm]
    · refine ⟨Int.toNat (-z), ?_⟩
      have hz' : z < 0 := lt_of_not_ge hz
      have hneg : (-z).toNat • p + z • p = 0 := by
        rw [← Int.toNat_of_nonneg (neg_nonneg.mpr (le_of_lt hz'))]
        simp [zsmul_natCast, add_comm, add_left_comm, add_assoc]
      simpa using hneg
