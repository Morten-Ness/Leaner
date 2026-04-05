import Mathlib

variable {K ι : Type*} {R : ι → Type*}

theorem smul_pi₀ [GroupWithZero K] [∀ i, MulAction K (R i)] {r : K} (S : Set ι) (t : ∀ i, Set (R i))
    (hr : r ≠ 0) : r • S.pi t = S.pi (r • t) := smul_pi (Units.mk0 r hr) S t

