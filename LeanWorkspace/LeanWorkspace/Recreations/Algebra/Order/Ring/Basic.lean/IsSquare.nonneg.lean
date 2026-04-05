import Mathlib

variable {α M R : Type*}

theorem IsSquare.nonneg [Semiring R] [LinearOrder R]
    [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R]
    {x : R} (h : IsSquare x) : 0 ≤ x := by
  rcases h with ⟨y, rfl⟩
  exact mul_self_nonneg y

