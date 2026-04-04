import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [S : AddTorsor V P] {ι : Sort*}

variable (k V)

variable (P)

variable {k V P}

variable (k V) {p₁ p₂ : P}

variable (P) in

variable {P}

theorem direction_sInf_of_mem_sInf (t : Set (AffineSubspace k P)) (p : P) (h : p ∈ sInf t) :
    AffineSubspace.direction (sInf t) = ⨅ s ∈ t, s.direction := AffineSubspace.direction_sInf_of_mem t p <| (AffineSubspace.mem_sInf_iff p t).mp h

