import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [S : AddTorsor V P] {ι : Sort*}

variable (k V)

variable (P)

variable {k V P}

variable (k V) {p₁ p₂ : P}

theorem span_union (s t : Set P) : affineSpan k (s ∪ t) = affineSpan k s ⊔ affineSpan k t := (AffineSubspace.gi k V P).gc.l_sup

