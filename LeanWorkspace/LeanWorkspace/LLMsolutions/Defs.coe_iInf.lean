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

theorem coe_iInf (s : ι → AffineSubspace k P) :
    ((iInf s : AffineSubspace k P) : Set P) = ⋂ i, s i := by
  ext p
  change p ∈ (iInf s : AffineSubspace k P) ↔ p ∈ ⋂ i, (s i : Set P)
  simp [Set.mem_iInter]
