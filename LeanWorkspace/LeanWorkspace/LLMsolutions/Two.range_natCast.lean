FAIL
import Mathlib

variable {R ι : Type*}

variable [AddMonoidWithOne R]

variable [CharP R 2]

theorem range_natCast : Set.range ((↑) : ℕ → R) = {0, 1} := by
  ext x
  constructor
  · rintro ⟨n, rfl⟩
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · left
      have h' : (n : R) = 0 := by
        rw [← Nat.cast_zero]
        exact CharP.cast_eq_zero_iff (R := R) 2 n |>.2 h
      exact h'
    · right
      have h' : (n : R) = 1 := by
        have hm : ((n - 1 : ℕ) : R) = 0 := by
          rw [← Nat.cast_zero]
          exact CharP.cast_eq_zero_iff (R := R) 2 (n - 1) |>.2 (by omega)
        have hn : (n : R) = ((n - 1 : ℕ) : R) + 1 := by
          rw [← Nat.cast_add, Nat.sub_add_cancel]
          omega
        rw [hn, hm, zero_add]
      exact h'
  · intro hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact ⟨0, by simp⟩
    · rcases Set.mem_singleton_iff.mp hx with rfl
      exact ⟨1, by simp⟩
