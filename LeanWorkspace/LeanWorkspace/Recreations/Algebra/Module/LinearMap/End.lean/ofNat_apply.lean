import Mathlib

variable {R R₂ S M M₁ M₂ M₃ N₁ : Type*}

variable [Semiring R] [AddCommMonoid M] [AddCommGroup N₁] [Module R M] [Module R N₁]

theorem ofNat_apply (n : ℕ) [n.AtLeastTwo] (m : M) :
    (ofNat(n) : Module.End R M) m = ofNat(n) • m := rfl

