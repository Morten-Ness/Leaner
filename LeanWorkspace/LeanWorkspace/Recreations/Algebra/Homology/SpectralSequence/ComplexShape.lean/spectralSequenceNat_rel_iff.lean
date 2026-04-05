import Mathlib

theorem spectralSequenceNat_rel_iff (u : ℤ × ℤ) (a b : ℕ × ℕ) :
    (ComplexShape.spectralSequenceNat u).Rel a b ↔ a.1 + u.1 = b.1 ∧ a.2 + u.2 = b.2 := Iff.rfl

