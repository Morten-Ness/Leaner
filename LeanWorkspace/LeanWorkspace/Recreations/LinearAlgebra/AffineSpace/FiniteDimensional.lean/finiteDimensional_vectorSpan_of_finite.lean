import Mathlib

variable (k : Type*) {V : Type*} {P : Type*}

variable {ι : Type*}

variable [DivisionRing k] [AddCommGroup V] [Module k V] [AddTorsor V P]

theorem finiteDimensional_vectorSpan_of_finite {s : Set P} (h : Set.Finite s) :
    FiniteDimensional k (vectorSpan k s) := .span_of_finite k <| h.vsub h

