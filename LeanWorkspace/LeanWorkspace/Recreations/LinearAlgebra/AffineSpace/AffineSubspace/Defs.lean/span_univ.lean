import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [S : AddTorsor V P] {ι : Sort*}

variable (k V)

variable (P)

theorem span_univ : affineSpan k (Set.univ : Set P) = ⊤ := eq_top_iff.2 <| subset_affineSpan k _

