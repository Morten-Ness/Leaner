import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [AddTorsor V P]

variable (P) in

theorem subset_spanPoints (s : Set P) : s ⊆ spanPoints k s := fun p => mem_spanPoints k p s

