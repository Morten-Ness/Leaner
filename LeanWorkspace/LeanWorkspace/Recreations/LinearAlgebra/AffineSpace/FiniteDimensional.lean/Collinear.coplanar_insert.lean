import Mathlib

variable {k : Type*} {V : Type*} {P : Type*}

variable [DivisionRing k] [AddCommGroup V] [Module k V] [AddTorsor V P]

variable (k) in

theorem Collinear.coplanar_insert {s : Set P} (h : Collinear k s) (p : P) :
    Coplanar k (insert p s) := by
  have : FiniteDimensional k { x // x ∈ vectorSpan k s } := h.finiteDimensional_vectorSpan
  grw [coplanar_iff_finrank_le_two, finrank_vectorSpan_insert_le_set, h.finrank_le_one]

