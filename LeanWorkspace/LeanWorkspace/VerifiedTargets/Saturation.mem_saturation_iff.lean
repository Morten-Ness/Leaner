import Mathlib

variable {M : Type*}

variable [CommMonoid M]

variable {s : Submonoid M} {x : M}

theorem mem_saturation_iff : x ∈ s.saturation ↔ ∃ y, x * y ∈ s := by
  refine ⟨fun h ↦ ?_, fun ⟨y, hxy⟩ ↦ (s.saturation.2 <| Submonoid.le_toSubmonoid_saturation hxy).1⟩
  induction h using Submonoid.saturation_induction with
  | mem _ hx => exact ⟨1, by simpa⟩
  | mul _ _ _ _ ih₁ ih₂ =>
    exact ih₁.elim fun y₁ h₁ ↦ ih₂.elim fun y₂ h₂ ↦
      ⟨y₁ * y₂, by rw [mul_mul_mul_comm]; exact mul_mem h₁ h₂⟩
  | of_mul x₁ x₂ _ ih =>
    exact ih.elim fun y h ↦ ⟨⟨x₂ * y, by rwa [← mul_assoc]⟩,
      ⟨x₁ * y, by rwa [mul_left_comm, ← mul_assoc]⟩⟩

