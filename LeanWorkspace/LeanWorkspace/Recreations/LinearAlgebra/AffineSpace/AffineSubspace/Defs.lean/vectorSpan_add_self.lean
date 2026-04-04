import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

theorem vectorSpan_add_self (s : Set V) : (vectorSpan k s : Set V) + s = affineSpan k s := by
  ext
  simp [mem_add, spanPoints]
  grind

