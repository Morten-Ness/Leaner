import Mathlib

variable {α : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α] {a b : α} {n : ℤ}

omit [IsStrictOrderedRing α] in
theorem Even.zpow_abs {p : ℤ} (hp : Even p) (a : α) : |a| ^ p = a ^ p := by
  rcases abs_choice a with h | h <;> simp only [h, hp.neg_zpow _]

