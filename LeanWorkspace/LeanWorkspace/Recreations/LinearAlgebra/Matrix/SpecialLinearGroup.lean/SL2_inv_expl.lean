import Mathlib

open scoped MatrixGroups

variable {n : Type u} [DecidableEq n] [Fintype n] {R : Type v} [CommRing R]

variable {S : Type*} [CommRing S]

theorem SL2_inv_expl (A : SL(2, R)) :
    A⁻¹ = ⟨![![A.1 1 1, -A.1 0 1], ![-A.1 1 0, A.1 0 0]], Matrix.SpecialLinearGroup.SL2_inv_expl_det A⟩ := by
  ext
  have := Matrix.adjugate_fin_two A.1
  rw [Matrix.SpecialLinearGroup.coe_inv, this]
  simp

