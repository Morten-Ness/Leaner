import Mathlib

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [hα : Archimedean α]
  {p : α} (hp : 0 < p)
  {a b c : α} {n : ℤ}

theorem toIcoMod_eq_self : toIcoMod hp a b = b ↔ b ∈ Set.Ico a (a + p) := by
  rw [toIcoMod_eq_iff, and_iff_left]
  exact ⟨0, by simp⟩

