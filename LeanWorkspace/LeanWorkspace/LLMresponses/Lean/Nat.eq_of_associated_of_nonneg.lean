FAIL
import Mathlib

theorem eq_of_associated_of_nonneg {a b : ℤ} (h : Associated a b) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a = b := by
  rcases h with ⟨u, rfl⟩
  rcases Int.units_eq_one_or u with hu | hu
  · subst hu
    simpa using (mul_one a).symm
  · subst hu
    have ha0 : a = 0 := by
      linarith
    subst ha0
    norm_num
