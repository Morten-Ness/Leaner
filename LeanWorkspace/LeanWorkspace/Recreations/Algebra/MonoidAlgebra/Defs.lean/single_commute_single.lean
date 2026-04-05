import Mathlib

variable {R S G M N O ι : Type*}

variable [Semiring R] {x y : R[M]} {r r₁ r₂ : R} {m m' m₁ m₂ : M}

variable [Mul M]

theorem single_commute_single (hm : Commute m₁ m₂) (hr : Commute r₁ r₂) :
    Commute (single m₁ r₁) (single m₂ r₂) := by simp [Commute, SemiconjBy, hm.eq, hr.eq]

