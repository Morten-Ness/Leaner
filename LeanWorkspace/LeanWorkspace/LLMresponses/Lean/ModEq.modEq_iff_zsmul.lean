FAIL
import Mathlib

variable {G : Type*} [AddCommGroup G] {p a a₁ a₂ b b₁ b₂ c : G} {n : ℕ} {z : ℤ}

theorem modEq_iff_zsmul : a ≡ b [PMOD p] ↔ ∃ m : ℤ, m • p = b - a := by
  constructor
  · intro h
    rcases h with ⟨m, hm⟩
    rcases hm with ⟨n, hmn⟩
    refine ⟨(m : ℤ) - n, ?_⟩
    have h1 : ((m : ℤ) • p + a) = (n : ℤ) • p + b := by
      simpa using hmn
    have h2 : (((m : ℤ) - n) • p) + a = b := by
      calc
        (((m : ℤ) - n) • p) + a = ((m : ℤ) • p - (n : ℤ) • p) + a := by simp [sub_eq_add_neg, sub_zsmul]
        _ = -((n : ℤ) • p) + (((m : ℤ) • p) + a) := by abel
        _ = -((n : ℤ) • p) + (((n : ℤ) • p) + b) := by rw [h1]
        _ = b := by abel
    exact eq_sub_iff_add_eq.mpr h2
  · rintro ⟨m, hm⟩
    refine ⟨Int.natAbs m, Int.natAbs (-m), ?_⟩
    have h' : m • p + a = b := by
      exact eq_sub_iff_add_eq.mp hm
    have hmabs : (Int.natAbs m : ℤ) • p - (Int.natAbs (-m) : ℤ) • p = m • p := by
      rw [← sub_zsmul]
      congr
      exact Int.natAbs_sub_natAbs_neg m
    calc
      Int.natAbs m • p + a = ((Int.natAbs m : ℤ) • p - (Int.natAbs (-m) : ℤ) • p) + ((Int.natAbs (-m) : ℤ) • p + a) := by abel
      _ = m • p + ((Int.natAbs (-m) : ℤ) • p + a) := by rw [hmabs]
      _ = (Int.natAbs (-m) : ℤ) • p + (m • p + a) := by abel
      _ = (Int.natAbs (-m) : ℤ) • p + b := by rw [h']
