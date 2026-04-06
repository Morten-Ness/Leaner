FAIL
import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [AddTorsor V P]

theorem direction_affineSpan_pair_le_iff_exists_smul {p₁ q₁ p₂ q₂ : P} :
    line[k, p₁, q₁].direction ≤ line[k, p₂, q₂].direction ↔ ∃ z : k, z • (q₂ -ᵥ p₂) = q₁ -ᵥ p₁ := by
  constructor
  · intro h
    have hq : q₁ ∈ line[k, p₁, q₁] := by
      exact AffineSubspace.right_mem_affineSpan_pair k p₁ q₁
    have hp : p₁ ∈ line[k, p₁, q₁] := by
      exact AffineSubspace.left_mem_affineSpan_pair k p₁ q₁
    have hmem : q₁ -ᵥ p₁ ∈ line[k, p₂, q₂].direction :=
      h (line[k, p₁, q₁]).vsub_mem_direction hq hp
    rw [AffineSubspace.mem_direction_iff_eq_vsub_right] at hmem
    rcases hmem with ⟨r, hr, hrv⟩
    rw [AffineSubspace.mem_line_iff_eq_smul_vsub p₂ q₂ r] at hr
    rcases hr with ⟨z, hz⟩
    refine ⟨z, ?_⟩
    rw [hz] at hrv
    simpa [vsub_vadd]
      using hrv
  · rintro ⟨z, hz⟩
    intro v hv
    rw [AffineSubspace.mem_direction_iff_eq_vsub_right] at hv ⊢
    rcases hv with ⟨r, hr, hvr⟩
    refine ⟨r, hr, ?_⟩
    rw [AffineSubspace.mem_line_iff_eq_smul_vsub p₂ q₂ r]
    refine ⟨1, by simp⟩
    rw [hvr, ← hz]
    simp [smul_smul]
