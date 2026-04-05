import Mathlib

theorem isCompl_even_odd : IsCompl { n : ℤ | Even n } { n | Odd n } := by
  simp [← not_even_iff_odd, ← Set.compl_setOf, isCompl_compl]

