FAIL
import Mathlib

open scoped Int

variable {G : Type*} [Group G] {A : Type*} [AddGroup A]

variable (H : Subgroup G)

theorem mem_normalizer_iff'' {g : G} : g ∈ Subgroup.normalizer H ↔ ∀ h : G, h ∈ H ↔ g⁻¹ * h * g ∈ H := by
  constructor
  · intro hg
    rw [Subgroup.mem_normalizer_iff] at hg
    intro h
    constructor
    · intro hh
      have hconj : g * (g⁻¹ * h * g) * g⁻¹ ∈ H := (hg (g⁻¹ * h * g)).2 hh
      simpa [mul_assoc] using hconj
    · intro hh
      have hconj : g * h * g⁻¹ ∈ H := by
        simpa [mul_assoc] using hh
      exact (hg h).1 hconj
  · intro hg
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have hh' : g⁻¹ * (g * h * g⁻¹) * g ∈ H := (hg (g * h * g⁻¹)).1 (by simpa [mul_assoc] using hh)
      simpa [mul_assoc] using hh'
    · intro hh
      have hh' : g⁻¹ * h * g ∈ H := by
        simpa [mul_assoc] using hh
      exact (hg h).2 hh'
