import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem ofFinsupp_erase (p : R[ℕ]) (n : ℕ) :
    (⟨p.erase n⟩ : R[X]) = (⟨p⟩ : R[X]).erase n := by
  simp only [erase_def]

