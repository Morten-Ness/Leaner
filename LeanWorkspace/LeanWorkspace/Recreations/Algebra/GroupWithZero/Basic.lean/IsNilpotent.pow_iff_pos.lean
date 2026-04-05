import Mathlib

variable {M₀ G₀ : Type*}

variable {R S : Type*} {x y : R}

theorem IsNilpotent.pow_iff_pos {n} {S : Type*} [MonoidWithZero S] {x : S} (hn : n ≠ 0) :
    IsNilpotent (x ^ n) ↔ IsNilpotent x := ⟨of_pow, (pow_of_pos · hn)⟩

