FAIL
import Mathlib

variable {α : Type u} {β : Type v}

theorem toFreeSemigroup_map (f : α → β) (x : FreeMagma α) :
    FreeMagma.toFreeSemigroup (FreeMagma.map f x) = FreeSemigroup.map f (FreeMagma.toFreeSemigroup x) := by
  induction x with
  | ih1 a =>
      rfl
  | ih2 x y ihx ihy =>
      simp [FreeMagma.map, FreeMagma.toFreeSemigroup, FreeSemigroup.map_mul, ihx, ihy]
