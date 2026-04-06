FAIL
import Mathlib

variable {R : Type*} [DivisionRing R] [CharZero R] {p : R}

theorem nsmul_mem_zmultiples_iff_exists_sub_div {r : R} {n : ℕ} (hn : n ≠ 0) :
    n • r ∈ AddSubgroup.zmultiples p ↔
      ∃ k : Fin n, r - (k : ℕ) • (p / n : R) ∈ AddSubgroup.zmultiples p := by
  constructor
  · intro hr
    refine ⟨⟨0, Nat.pos_of_ne_zero hn⟩, ?_⟩
    simpa using hr
  · rintro ⟨k, hk⟩
    rcases hk with ⟨m, hm⟩
    refine ⟨m * n + k, ?_⟩
    have hnR : (n : R) ≠ 0 := by
      exact_mod_cast hn
    calc
      ((m * n + k : ℤ) • p : R)
          = (m * n : ℤ) • p + (k : ℤ) • p := by rw [add_zsmul]
      _ = n • (m • p : R) + (k : ℤ) • p := by rw [Int.mul_ediv_assoc_zsmul]
      _ = n • (r - (k : ℕ) • (p / n : R)) + (k : ℤ) • p := by rw [hm]
      _ = n • r - n • ((k : ℕ) • (p / n : R)) + (k : ℤ) • p := by
            rw [nsmul_sub]
      _ = n • r - ((n * k : ℕ) • (p / n : R)) + (k : ℤ) • p := by
            rw [nsmul_eq_mul, nsmul_eq_mul, nsmul_eq_mul]
            simp [Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm]
      _ = n • r - ((k : ℕ) : R) * p + (k : ℤ) • p := by
            rw [nsmul_eq_mul]
            congr 2
            calc
              ((n * k : ℕ) : R) * (p / n : R)
                  = (((k : ℕ) : R) * (n : R)) * (p / n : R) := by
                      norm_num [Nat.cast_mul, mul_comm, mul_left_comm, mul_assoc]
              _ = ((k : ℕ) : R) * ((n : R) * (p / n : R)) := by ring
              _ = ((k : ℕ) : R) * p := by rw [mul_div_cancel₀ _ hnR]
      _ = n • r := by
            rw [zsmul_eq_mul]
            norm_num
