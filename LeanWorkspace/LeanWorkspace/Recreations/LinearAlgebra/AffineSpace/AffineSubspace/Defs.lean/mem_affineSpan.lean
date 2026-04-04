import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

theorem mem_affineSpan {p : P} {s : Set P} (hp : p ∈ s) : p ∈ affineSpan k s := mem_spanPoints k p s hp

