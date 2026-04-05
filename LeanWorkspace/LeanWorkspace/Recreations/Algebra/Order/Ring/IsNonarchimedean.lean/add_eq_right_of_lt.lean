import Mathlib

variable {R : Type*} [Semiring R] [LinearOrder R] {a b : R} {m n : ℕ}

theorem add_eq_right_of_lt {F α : Type*} [AddGroup α] [FunLike F α R]
    [AddGroupSeminormClass F α R] {f : F} (hna : IsNonarchimedean f) {x y : α}
    (h_lt : f x < f y) : f (x + y) = f y := by
  by_contra! h
  have h1 : f (x + y) ≤ f y := (hna x y).trans_eq (max_eq_right_of_lt h_lt)
  apply lt_irrefl (f y)
  calc
    f y = f (-x + (x + y)) := by simp
    _   ≤ max (f (-x)) (f (x + y)) := hna (-x) (x + y)
    _   < max (f y) (f y) := by
      rw [max_self, map_neg_eq_map]
      exact max_lt h_lt <| lt_of_le_of_ne h1 h
    _   = f y := max_self (f y)

set_option linter.style.whitespace false in -- manual alignment is not recognised

