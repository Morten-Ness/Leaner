import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [S : AddTorsor V P] {ι : Sort*}

variable (k V)

variable (P)

variable {k V P}

theorem _root_.affineSpan_le {s : Set P} {Q : AffineSubspace k P} :
    affineSpan k s ≤ Q ↔ s ⊆ (Q : Set P) := (AffineSubspace.gi k V P).gc _ _

