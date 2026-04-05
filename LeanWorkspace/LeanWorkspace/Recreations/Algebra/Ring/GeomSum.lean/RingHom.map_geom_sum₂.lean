import Mathlib

variable {R S : Type*}

variable [Semiring R] [Semiring S] {x y : R}

theorem RingHom.map_geom_sum₂ (x y : R) (n : ℕ) (f : R →+* S) :
    f (∑ i ∈ range n, x ^ i * y ^ (n - 1 - i)) = ∑ i ∈ range n, f x ^ i * f y ^ (n - 1 - i) := by
  simp [map_sum f]

