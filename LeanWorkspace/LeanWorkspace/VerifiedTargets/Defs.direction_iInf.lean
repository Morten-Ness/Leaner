import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [S : AddTorsor V P] {ι : Sort*}

variable (k V)

variable (P)

variable {k V P}

variable (k V) {p₁ p₂ : P}

variable (P) in

variable {P}

theorem direction_iInf (s : ι → AffineSubspace k P) :
    (iInf s).direction ≤ ⨅ i, (s i).direction := by
  apply (AffineSubspace.direction_sInf _).trans_eq
  rw [iInf_range]

