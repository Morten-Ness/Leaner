import Mathlib

variable {R S M N : Type*}

variable [Ring R] [AddCommGroup M] [Module R M] {m : M} {r₁ r₂ : R}

theorem Module.isTorsionFree_iff_smul_eq_zero [IsDomain R] :
    IsTorsionFree R M ↔ ∀ (r : R) (m : M), r • m = 0 → r = 0 ∨ m = 0 where
  mp _ _ _ := smul_eq_zero.1
  mpr := .of_smul_eq_zero

