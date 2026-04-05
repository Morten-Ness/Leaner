import Mathlib

variable {M₀ G₀ : Type*}

variable {R S : Type*} {x y : R}

theorem eq_zero_of_pow_eq_zero [Zero R] [Pow R ℕ] [IsReduced R] {n : ℕ} (h : x ^ n = 0) :
    x = 0 := IsReduced.eq_zero x ⟨n, h⟩

