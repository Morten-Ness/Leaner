import Mathlib

variable {M : Type*}

variable [Group M] [Lattice M]

theorem le_def {a b : MulArchimedeanOrder M} : a ≤ b ↔ ∃ n, |b.val|ₘ ≤ |a.val|ₘ ^ n := .rfl

