FAIL
import Mathlib

variable {R S : Type*}

variable (R) [Ring R] [NoZeroDivisors R] [Nontrivial R] [Finite R]

theorem prime_ringChar : Nat.Prime (ringChar R) := by
  let p := ringChar R
  have hp0 : p ≠ 0 := by
    exact ne_of_gt (ringChar_pos R)
  rw [Nat.prime_iff]
  constructor
  · exact Nat.succ_le_of_lt (ringChar_pos R)
  · intro m hm hmd
    by_cases hm1 : m = 1
    · exact Or.inl hm1
    · right
      have hm0 : m ≠ 0 := by
        intro hmz
        subst hmz
        simp at hmd
      have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
      obtain ⟨k, hk⟩ := hmd
      have hk0 : k ≠ 0 := by
        intro hk0
        subst hk0
        simp at hk
        exact hp0 hk.symm
      have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
      have hmk : 1 < m := Nat.lt_of_le_of_ne hm hm1.symm
      have hkge : 1 ≤ k := Nat.succ_le_of_lt hkpos
      by_contra hkne
      have hk1 : k = 1 := Nat.eq_one_of_dvd_one <| by
        have hzero : ((m : R) * (k : R)) = 0 := by
          change ((m * k : Nat) : R) = 0
          rw [hk, Nat.cast_ringChar]
        have hmz : (m : R) = 0 := by
          apply eq_zero_or_eq_zero_of_mul_eq_zero hzero |>.resolve_right
          intro hkz
          apply hkne
          rw [← Nat.cast_eq_zero]
          exact hkz
        have hpdvdm : p ∣ m := by
          rw [← Nat.cast_eq_zero]
          exact hmz
        have hplem : p ≤ m := Nat.le_of_dvd hmpos hpdvdm
        rw [hk] at hplem
        have : k ≤ 1 := by omega
        exact this
      exact Or.inr <| by simpa [hk1] using hk.symm
