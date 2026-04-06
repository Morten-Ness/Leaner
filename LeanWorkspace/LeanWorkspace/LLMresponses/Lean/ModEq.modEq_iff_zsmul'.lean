FAIL
import Mathlib

variable {G : Type*} [AddCommGroup G] {p a a₁ a₂ b b₁ b₂ c : G} {n : ℕ} {z : ℤ}

theorem modEq_iff_zsmul' : a ≡ b [PMOD p] ↔ ∃ m : ℤ, b - a = m • p := by
  constructor
  · intro h
    rcases h with ⟨m, n, hmn⟩
    refine ⟨m - n, ?_⟩
    have h1 : b = (m - n) • p + a := by
      calc
        b = -(n • p) + (n • p + b) := by abel
        _ = -(n • p) + (m • p + a) := by rw [hmn]
        _ = (m - n) • p + a := by
          rw [sub_eq_add_neg, sub_zsmul, add_assoc]
    calc
      b - a = ((m - n) • p + a) - a := by rw [h1]
      _ = (m - n) • p := by abel
  · rintro ⟨m, hm⟩
    refine ⟨Int.natAbs m, Int.natAbs (-m), ?_⟩
    have hz : (m : ℤ) = Int.natAbs m - Int.natAbs (-m) := by
      simpa [Int.subNatNat_eq_coe, Int.natAbs_ofNat, Int.natAbs_neg] using Int.ofNat_natAbs_eq_of_nonneg (Int.le_add_neg_iff.mp le_rfl)
    have hp : (m • p : G) = Int.natAbs m • p - Int.natAbs (-m) • p := by
      rw [hz, sub_eq_add_neg, sub_zsmul]
    have hb : b = m • p + a := by
      calc
        b = (b - a) + a := by abel
        _ = m • p + a := by rw [hm]
    calc
      Int.natAbs m • p + a
          = (Int.natAbs (-m) • p + m • p) + a := by
              rw [hp]
              abel
      _ = Int.natAbs (-m) • p + (m • p + a) := by abel
      _ = Int.natAbs (-m) • p + b := by rw [hb]
