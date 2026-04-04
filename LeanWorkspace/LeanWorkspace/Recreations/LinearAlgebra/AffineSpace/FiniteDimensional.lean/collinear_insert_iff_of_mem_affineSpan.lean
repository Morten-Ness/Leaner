import Mathlib

variable (k : Type*) {V : Type*} {P : Type*}

variable {ι : Type*}

variable [DivisionRing k] [AddCommGroup V] [Module k V] [AddTorsor V P]

variable {k}

variable (k)

variable (k P)

variable {P}

variable (k) in

theorem collinear_insert_iff_of_mem_affineSpan {s : Set P} {p : P} (h : p ∈ affineSpan k s) :
    Collinear k (insert p s) ↔ Collinear k s := by
  rw [Collinear, Collinear, vectorSpan_insert_eq_vectorSpan h]

