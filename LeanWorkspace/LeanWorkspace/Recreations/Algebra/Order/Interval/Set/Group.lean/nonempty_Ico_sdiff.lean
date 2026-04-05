import Mathlib

variable {α : Type*}

variable [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]

theorem nonempty_Ico_sdiff {x dx y dy : α} (h : dy < dx) (hx : 0 < dx) :
    Nonempty ↑(Ico x (x + dx) \ Ico y (y + dy)) := by
  rcases lt_or_ge x y with h' | h'
  · use x
    simp [*, not_le.2 h']
  · use max x (x + dy)
    simp [*]

