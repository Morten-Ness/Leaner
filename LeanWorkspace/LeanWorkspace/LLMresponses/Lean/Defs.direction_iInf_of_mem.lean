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

theorem direction_iInf_of_mem (s : ι → AffineSubspace k P) (p : P) (h : ∀ i, p ∈ s i) :
    (iInf s).direction = ⨅ i, (s i).direction := by
  let t : AffineSubspace k P := AffineSubspace.mk' p (⨅ i, (s i).direction)
  have hp_t : p ∈ t := by
    simp [t]
  have hle : t ≤ iInf s := by
    intro q hq i
    have hqdir : q -ᵥ p ∈ ⨅ i, (s i).direction := by
      simpa [t] using hq
    have hqdir_i : q -ᵥ p ∈ (s i).direction := by
      exact (Submodule.mem_iInf.mp hqdir) i
    exact (s i).vsub_right_mem_direction_iff_mem.mp <| by
      simpa using hqdir_i
  have hge : iInf s ≤ t := by
    intro q hq
    have hq_i : ∀ i, q ∈ s i := by
      intro i
      exact hq i
    have hqdir_i : ∀ i, q -ᵥ p ∈ (s i).direction := by
      intro i
      exact (s i).vsub_right_mem_direction_iff_mem.mpr ⟨h (i), hq_i i, rfl⟩
    have hqdir : q -ᵥ p ∈ ⨅ i, (s i).direction := by
      exact Submodule.mem_iInf.mpr hqdir_i
    simpa [t] using hqdir
  have ht : t = iInf s := le_antisymm hle hge
  calc
    (iInf s).direction = t.direction := by simpa [ht]
    _ = ⨅ i, (s i).direction := by
      simp [t]
