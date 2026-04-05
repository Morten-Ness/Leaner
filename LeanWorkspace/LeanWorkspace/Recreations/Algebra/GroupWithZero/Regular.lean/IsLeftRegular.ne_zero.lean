import Mathlib

variable [MulZeroClass R] {a b : R}

theorem IsLeftRegular.ne_zero [Nontrivial R] (la : IsLeftRegular a) : a ≠ 0 := by
  rintro rfl
  rcases exists_pair_ne R with ⟨x, y, xy⟩
  refine xy (la ?_)
  simp

