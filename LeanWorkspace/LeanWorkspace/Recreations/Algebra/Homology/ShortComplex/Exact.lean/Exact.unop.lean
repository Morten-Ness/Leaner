import Mathlib

variable {C D : Type*} [Category* C] [Category* D]

theorem Exact.unop {S : CategoryTheory.ShortComplex Cᵒᵖ} (h : S.Exact) : S.unop.Exact := by
  obtain ⟨h, z⟩ := h
  exact ⟨⟨h.unop, (IsZero.of_iso z h.iso.symm).unop⟩⟩

