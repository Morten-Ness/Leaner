import Mathlib

variable {ι α β M N P G : Type*}

theorem ranges_flatten : ∀ (l : List ℕ), l.ranges.flatten = range l.sum
  | [] => rfl
  | a :: l => by simp [ranges, ← map_flatten, ranges_flatten, range_add]
