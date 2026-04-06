FAIL
import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [S : AddTorsor V P] {ι : Sort*}

variable (k V)
variable (P)
variable {k V P}
variable (k V) {p₁ p₂ : P}
variable (P) in
theorem direction_iInf_of_mem_iInf (s : ι → AffineSubspace k P) (p : P) (h : p ∈ iInf s) :
    (iInf s).direction = ⨅ i, (s i).direction := by
  simpa [AffineSubspace.mem_iInf] using
    (AffineSubspace.direction_iInf_of_mem (s := s) (p := p) h)
