import Mathlib

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [hα : Archimedean α]
  {p : α} (hp : 0 < p)
  {a b c : α} {n : ℤ}

theorem toIocMod_eq_self : toIocMod hp a b = b ↔ b ∈ Set.Ioc a (a + p) := by
  rw [toIocMod_eq_iff, and_iff_left]
  exact ⟨0, by simp⟩

