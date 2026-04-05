import Mathlib

variable {R A : Type*} [Semiring R]

variable [StarAddMonoid R] [Star A] {a : A}

theorem _root_.IsSelfAdjoint.inr (ha : IsSelfAdjoint a) : IsSelfAdjoint (a : Unitization R A) := Unitization.isSelfAdjoint_inr.mpr ha

