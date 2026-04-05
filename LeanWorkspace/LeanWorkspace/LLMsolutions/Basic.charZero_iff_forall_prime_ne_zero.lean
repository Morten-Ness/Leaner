FAIL
import Mathlib

variable (R : Type*)

theorem charZero_iff_forall_prime_ne_zero [NonAssocRing R] [NoZeroDivisors R] [Nontrivial R] :
    CharZero R ↔ ∀ p : ℕ, p.Prime → (p : R) ≠ 0 := by
  constructor
  · intro _ p hp
    exact_mod_cast hp.ne_zero
  · intro h
    refine ⟨?_⟩
    intro m n hmn
    by_cases hm : m = n
    · exact hm
    · have hlt_or_gt : m < n ∨ n < m := lt_or_gt_of_ne hm
      cases hlt_or_gt with
      | inl hlt =>
          have hsub : ((n - m : ℕ) : R) = 0 := by
            rw [Nat.cast_sub hlt.le]
            simpa [hmn]
          have hnm2 : 2 ≤ n - m := by
            omega
          obtain ⟨p, hpprime, hpdvd⟩ := Nat.exists_prime_and_dvd hnm2
          have hpcastdvd : (p : R) ∣ ((n - m : ℕ) : R) := by
            rcases hpdvd with ⟨k, rfl⟩
            refine ⟨(k : R), by simp [Nat.cast_mul, mul_comm, mul_left_comm, mul_assoc]⟩
          have hp0 : (p : R) = 0 := eq_zero_of_dvd_of_zero hpcastdvd hsub
          exact (h p hpprime hp0).elim
      | inr hgt =>
          have hsub : ((m - n : ℕ) : R) = 0 := by
            rw [Nat.cast_sub hgt.le]
            simpa [hmn]
          have hmn2 : 2 ≤ m - n := by
            omega
          obtain ⟨p, hpprime, hpdvd⟩ := Nat.exists_prime_and_dvd hmn2
          have hpcastdvd : (p : R) ∣ ((m - n : ℕ) : R) := by
            rcases hpdvd with ⟨k, rfl⟩
            refine ⟨(k : R), by simp [Nat.cast_mul, mul_comm, mul_left_comm, mul_assoc]⟩
          have hp0 : (p : R) = 0 := eq_zero_of_dvd_of_zero hpcastdvd hsub
          exact (h p hpprime hp0).elim
