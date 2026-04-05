import Mathlib

variable {R S M M₂ : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M]

theorem ofNat_smul_eq_nsmul (n : ℕ) [n.AtLeastTwo] (b : M) :
    (ofNat(n) : R) • b = ofNat(n) • b := Nat.cast_smul_eq_nsmul ..

