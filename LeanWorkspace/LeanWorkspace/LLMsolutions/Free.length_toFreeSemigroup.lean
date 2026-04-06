import Mathlib

variable {α : Type u} {β : Type v}

theorem length_toFreeSemigroup (x : FreeMagma α) : (FreeMagma.toFreeSemigroup x).length = x.length := by
  induction x with
  | ih1 a =>
      rfl
  | ih2 x y ihx ihy =>
      simpa [FreeMagma.toFreeSemigroup, FreeMagma.length] using congrArg₂ Nat.add ihx ihy
