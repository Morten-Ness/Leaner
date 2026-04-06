FAIL
import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [S : AddTorsor V P] {ι : Sort*}

variable (k V)

variable (P)

variable {k V P}

variable (k V) {p₁ p₂ : P}

variable (P) in

theorem direction_top : (⊤ : AffineSubspace k P).direction = ⊤ := by
  ext v
  constructor
  · intro hv
    trivial
  · intro hv
    rw [AffineSubspace.mem_direction_iff_eq_vsub_right]
    simp
