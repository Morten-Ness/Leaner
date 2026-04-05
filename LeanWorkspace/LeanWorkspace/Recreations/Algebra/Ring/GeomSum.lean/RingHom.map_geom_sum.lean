import Mathlib

variable {R S : Type*}

variable [Semiring R] [Semiring S] {x y : R}

theorem RingHom.map_geom_sum (x : R) (n : ℕ) (f : R →+* S) :
    f (∑ i ∈ range n, x ^ i) = ∑ i ∈ range n, f x ^ i := by simp [map_sum f]

