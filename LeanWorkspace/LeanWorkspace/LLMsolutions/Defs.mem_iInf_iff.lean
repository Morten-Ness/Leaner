FAIL
import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [S : AddTorsor V P] {ι : Sort*}

variable (k V)
variable (P)
variable {k V P}
variable (k V) {p₁ p₂ : P}
variable (P) in
variable {P}

theorem mem_iInf_iff (s : ι → AffineSubspace k P) (p : P) : p ∈ iInf s ↔ ∀ i, p ∈ s i := by
  constructor
  · intro hp i
    exact hp i
  · intro hp
    exact hp
