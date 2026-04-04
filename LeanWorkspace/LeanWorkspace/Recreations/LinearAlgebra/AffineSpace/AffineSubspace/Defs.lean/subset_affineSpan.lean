import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

theorem subset_affineSpan (s : Set P) : s ⊆ affineSpan k s := subset_spanPoints k s

