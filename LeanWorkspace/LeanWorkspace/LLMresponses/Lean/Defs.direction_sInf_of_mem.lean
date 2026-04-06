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

theorem direction_sInf_of_mem (t : Set (AffineSubspace k P)) (p : P) (h : ∀ s ∈ t, p ∈ s) :
    AffineSubspace.direction (sInf t) = ⨅ s ∈ t, s.direction := by
  classical
  ext v
  constructor
  · intro hv
    rw [Submodule.mem_iInf]
    intro s
    rw [Submodule.mem_iInf]
    intro hs
    rw [AffineSubspace.mem_direction_iff_eq_vsub_right]
    exact s.vsub_mem_direction (h s hs) (by
      simpa [vadd_vsub] using s.vadd_mem_of_mem_direction (h s hs) hv)
  · intro hv
    rw [AffineSubspace.mem_direction_iff_eq_vsub_right]
    change v +ᵥ p ∈ sInf t
    intro s hs
    have hvs : v ∈ s.direction := by
      rw [Submodule.mem_iInf] at hv
      exact (hv s).2 hs
    exact s.vadd_mem_of_mem_direction (h s hs) hvs
