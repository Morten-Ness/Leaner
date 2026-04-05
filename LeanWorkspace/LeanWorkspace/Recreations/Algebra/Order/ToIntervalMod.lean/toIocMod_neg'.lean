import Mathlib

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [hα : Archimedean α]
  {p : α} (hp : 0 < p)
  {a b c : α} {n : ℤ}

theorem toIocMod_neg' (a b : α) : toIocMod hp (-a) b = p - toIcoMod hp a (-b) := by
  simpa only [neg_neg] using toIocMod_neg hp (-a) (-b)

