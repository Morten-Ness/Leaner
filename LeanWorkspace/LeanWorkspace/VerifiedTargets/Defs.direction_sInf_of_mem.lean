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
  apply (AffineSubspace.direction_sInf t).antisymm
  intro v hv
  rw [← AffineSubspace.vadd_mem_iff_mem_direction v ((AffineSubspace.mem_sInf_iff p t).mpr h), AffineSubspace.mem_sInf_iff]
  intro s hs
  rw [AffineSubspace.vadd_mem_iff_mem_direction v (h s hs)]
  simp only [Submodule.mem_iInf] at hv
  exact hv s hs

