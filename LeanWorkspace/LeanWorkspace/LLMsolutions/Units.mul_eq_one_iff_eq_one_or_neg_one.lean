FAIL
import Mathlib

variable {u v : ℤ}

theorem mul_eq_one_iff_eq_one_or_neg_one : u * v = 1 ↔ u = 1 ∧ v = 1 ∨ u = -1 ∧ v = -1 := by
  constructor
  · intro h
    have hu_dvd : u ∣ 1 := ⟨v, h⟩
    have hv_dvd : v ∣ 1 := ⟨u, by simpa [mul_comm] using h⟩
    have hu_eq : u = 1 ∨ u = -1 := by
      have := Int.eq_one_or_neg_one_of_dvd_one hu_dvd
      simpa using this
    have hv_eq : v = 1 ∨ v = -1 := by
      have := Int.eq_one_or_neg_one_of_dvd_one hv_dvd
      simpa using this
    rcases hu_eq with rfl | rfl
    · rcases hv_eq with rfl | rfl
      · exact Or.inl ⟨rfl, rfl⟩
      · exfalso
        norm_num at h
    · rcases hv_eq with rfl | rfl
      · exfalso
        norm_num at h
      · exact Or.inr ⟨rfl, rfl⟩
  · intro h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num
