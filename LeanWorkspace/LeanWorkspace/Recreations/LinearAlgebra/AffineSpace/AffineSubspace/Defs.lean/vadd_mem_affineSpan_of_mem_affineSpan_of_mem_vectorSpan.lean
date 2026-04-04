import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {k}

theorem vadd_mem_affineSpan_of_mem_affineSpan_of_mem_vectorSpan {s : Set P} {p : P} {v : V}
    (hp : p ∈ affineSpan k s) (hv : v ∈ vectorSpan k s) : v +ᵥ p ∈ affineSpan k s := vadd_mem_spanPoints_of_mem_spanPoints_of_mem_vectorSpan k hp hv

