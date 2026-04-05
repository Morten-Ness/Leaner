import Mathlib

variable {M N P σ : Type*}

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

theorem coe_prod (s : Subsemigroup M) (t : Subsemigroup N) :
    (s.prod t : Set (M × N)) = (s : Set M) ×ˢ (t : Set N) := rfl

