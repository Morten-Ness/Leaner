import Mathlib

set_option backward.isDefEq.respectTransparency false in
theorem negOnePow_neg (n : ℤ) : (-n).negOnePow = n.negOnePow := by
  dsimp [Int.negOnePow]
  simp only [zpow_neg, ← inv_zpow, inv_neg, inv_one]

