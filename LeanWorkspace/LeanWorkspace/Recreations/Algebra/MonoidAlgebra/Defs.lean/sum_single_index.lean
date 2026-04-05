import Mathlib

variable {R S G M N O ι : Type*}

variable [Semiring R] {x y : R[M]} {r r₁ r₂ : R} {m m' m₁ m₂ : M}

theorem sum_single_index [AddCommMonoid N] {m : M} {r : R} {h : M → R → N} (h_zero : h m 0 = 0) :
    (single m r).sum h = h m r := by
  simp [h_zero]

