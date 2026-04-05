import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [S : AddTorsor V P] {ι : Sort*}

variable (k V)

variable (P)

variable {k V P}

variable (k V) {p₁ p₂ : P}

theorem span_iUnion {ι : Type*} (s : ι → Set P) :
    affineSpan k (⋃ i, s i) = ⨆ i, affineSpan k (s i) := (AffineSubspace.gi k V P).gc.l_iSup

