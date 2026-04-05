import Mathlib

variable {R : Type*} [Semiring R] [LinearOrder R] {a b : R} {m n : ℕ}

theorem add_eq_max_of_ne {F α : Type*} [AddGroup α] [FunLike F α R]
    [AddGroupSeminormClass F α R] {f : F} (hna : IsNonarchimedean f) {x y : α} (hne : f x ≠ f y) :
    f (x + y) = max (f x) (f y) := by
  rcases hne.lt_or_gt with h_lt | h_lt
  · rw [IsNonarchimedean.add_eq_right_of_lt hna h_lt]
    exact (max_eq_right_of_lt h_lt).symm
  · rw [IsNonarchimedean.add_eq_left_of_lt hna h_lt]
    exact (max_eq_left_of_lt h_lt).symm

