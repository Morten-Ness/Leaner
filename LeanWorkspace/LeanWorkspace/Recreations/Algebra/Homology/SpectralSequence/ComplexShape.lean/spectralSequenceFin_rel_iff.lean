import Mathlib

theorem spectralSequenceFin_rel_iff {l : ℕ} (u : ℤ × ℤ) (a b : ℤ × Fin l) :
    (ComplexShape.spectralSequenceFin l u).Rel a b ↔ a.1 + u.1 = b.1 ∧ a.2 + u.2 = b.2 := Iff.rfl

