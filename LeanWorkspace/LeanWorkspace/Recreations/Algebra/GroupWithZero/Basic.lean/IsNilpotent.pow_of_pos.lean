import Mathlib

variable {M₀ G₀ : Type*}

variable {R S : Type*} {x y : R}

theorem IsNilpotent.pow_of_pos {n} {S : Type*} [MonoidWithZero S] {x : S}
    (hx : IsNilpotent x) (hn : n ≠ 0) : IsNilpotent (x ^ n) := by
  cases n with
  | zero => contradiction
  | succ => exact IsNilpotent.pow_succ _ hx

