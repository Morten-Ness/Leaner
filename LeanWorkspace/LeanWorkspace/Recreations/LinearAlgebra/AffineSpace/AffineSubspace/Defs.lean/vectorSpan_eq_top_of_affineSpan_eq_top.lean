import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [S : AddTorsor V P] {ι : Sort*}

variable (k V)

variable (P)

variable {k V P}

variable (k V) {p₁ p₂ : P}

variable (P) in

theorem vectorSpan_eq_top_of_affineSpan_eq_top {s : Set P} (h : affineSpan k s = ⊤) :
    vectorSpan k s = ⊤ := by rw [← direction_affineSpan, h, AffineSubspace.direction_top]

