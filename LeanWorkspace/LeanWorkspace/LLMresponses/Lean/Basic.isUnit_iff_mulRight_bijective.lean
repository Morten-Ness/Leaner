FAIL
import Mathlib

variable {α : Type u}

variable {M : Type*}

variable [Monoid M] {a b c : M}

theorem isUnit_iff_mulRight_bijective {a : M} :
    IsUnit a ↔ Function.Bijective (· * a) := by
  constructor
  · intro ha
    rcases ha with ⟨u, rfl⟩
    constructor
    · intro x y h
      have h' : (x : M) * ↑u * ↑(u⁻¹) = y * ↑u * ↑(u⁻¹) := by
        simpa [h]
      simpa [mul_assoc] using h'
    · intro y
      refine ⟨y * ↑(u⁻¹), ?_⟩
      simp [mul_assoc]
  · intro h
    rcases h.2 1 with ⟨b, hb⟩
    refine ⟨⟨a, b, ?_, hb⟩, rfl⟩
    have h1 : (b * a) * b = 1 * b := by rw [hb]
    have h2 : b * (a * b) = 1 * b := by simpa [mul_assoc] using h1
    have h3 : a * b = 1 := by
      have := h.1 h2
      simpa using this
    exact h3
