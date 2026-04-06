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

theorem direction_iInf (s : ι → AffineSubspace k P) :
    (iInf s).direction ≤ ⨅ i, (s i).direction := by
  refine le_iInf ?_
  intro i
  change (iInf s).direction ≤ (s i).direction
  intro v hv
  rw [AffineSubspace.mem_direction_iff_eq_vsub_right] at hv ⊢
  intro p hp
  exact (iInf_le s i) (hv p hp)
