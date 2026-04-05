import Mathlib

variable {R S M N : Type*}

variable [Ring R] [AddCommGroup M] [Module R M] {m : M} {r₁ r₂ : R}

theorem Module.IsTorsionFree.of_smul_eq_zero [Nontrivial R]
    (h : ∀ (r : R) (m : M), r • m = 0 → r = 0 ∨ m = 0) :
    IsTorsionFree R M where
  isSMulRegular r hr m₁ m₂ hm := by
    simpa [sub_eq_zero, hr.ne_zero] using h r (m₁ - m₂) (by simpa [smul_sub, sub_eq_zero] using hm)

