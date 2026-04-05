import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

theorem weightedVSubOfPoint_vadd (s : Finset ι) (w : ι → k) (p : ι → P) (b : P) (v : V) :
    s.weightedVSubOfPoint (v +ᵥ p) b w = s.weightedVSubOfPoint p (-v +ᵥ b) w := by
  simp [vadd_vsub_assoc, vsub_vadd_eq_vsub_sub, add_comm]

