import Mathlib

variable {C : Type*} [Category* C] [Preadditive C]

variable {S₁ S₂ S₃ : ShortComplex C}

variable (φ₁ φ₂ φ₃ φ₄ : S₁ ⟶ S₂)

theorem eq_add_nullHomotopic (h : CategoryTheory.ShortComplex.Homotopy φ₁ φ₂) :
    φ₁ = φ₂ + CategoryTheory.ShortComplex.nullHomotopic _ _ h.h₀ h.h₀_f h.h₁ h.h₂ h.h₃ h.g_h₃ := by
  ext
  · dsimp; rw [h.comm₁]; abel
  · dsimp; rw [h.comm₂]; abel
  · dsimp; rw [h.comm₃]; abel

