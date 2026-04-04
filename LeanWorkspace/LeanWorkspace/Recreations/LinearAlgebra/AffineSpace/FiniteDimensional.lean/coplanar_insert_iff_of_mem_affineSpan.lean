import Mathlib

variable (k : Type*) {V : Type*} {P : Type*}

variable {ι : Type*}

variable [DivisionRing k] [AddCommGroup V] [Module k V] [AddTorsor V P]

variable {k}

variable (k)

variable (k P)

variable {P}

variable (k) in

variable (k) (P)

theorem coplanar_insert_iff_of_mem_affineSpan {s : Set P} {p : P} (h : p ∈ affineSpan k s) :
    Coplanar k (insert p s) ↔ Coplanar k s := by
  rw [Coplanar, Coplanar, vectorSpan_insert_eq_vectorSpan h]

