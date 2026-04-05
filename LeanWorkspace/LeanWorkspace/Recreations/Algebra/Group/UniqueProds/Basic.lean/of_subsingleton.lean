import Mathlib

variable {G H : Type*} [Mul G] [Mul H] {A B : Finset G} {a0 b0 : G}

theorem of_subsingleton [Subsingleton G] : UniqueMul A B a0 b0 := by
  simp [UniqueMul, eq_iff_true_of_subsingleton]

