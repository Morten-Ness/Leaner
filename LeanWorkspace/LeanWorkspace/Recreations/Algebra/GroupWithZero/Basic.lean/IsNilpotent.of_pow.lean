import Mathlib

variable {M₀ G₀ : Type*}

variable {R S : Type*} {x y : R}

theorem IsNilpotent.of_pow [MonoidWithZero R] {x : R} {m : ℕ}
    (h : IsNilpotent (x ^ m)) : IsNilpotent x := have ⟨n, h⟩ := h
  ⟨m * n, by rw [← h, pow_mul x m n]⟩

