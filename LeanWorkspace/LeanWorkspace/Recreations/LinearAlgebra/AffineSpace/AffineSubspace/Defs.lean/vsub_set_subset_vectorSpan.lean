import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [AddTorsor V P]

variable (P) in

theorem vsub_set_subset_vectorSpan (s : Set P) : s -ᵥ s ⊆ ↑(vectorSpan k s) := Submodule.subset_span

