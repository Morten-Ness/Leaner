import Mathlib

variable {M : Type*}

variable [Group M] [Lattice M]

theorem lt_def {a b : MulArchimedeanOrder M} : a < b ↔ ∀ n, |b.val|ₘ ^ n < |a.val|ₘ := .rfl

