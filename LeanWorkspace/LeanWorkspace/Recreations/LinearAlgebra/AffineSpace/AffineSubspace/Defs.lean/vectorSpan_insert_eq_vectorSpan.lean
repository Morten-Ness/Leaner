import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {ι : Type*}

variable {k}

variable (k)

theorem vectorSpan_insert_eq_vectorSpan {p : P} {ps : Set P} (h : p ∈ affineSpan k ps) :
    vectorSpan k (insert p ps) = vectorSpan k ps := by
  simp_rw [← direction_affineSpan, affineSpan_insert_eq_affineSpan _ h]

