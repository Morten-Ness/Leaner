import Mathlib

open scoped MatrixGroups

variable {n : Type u} [DecidableEq n] [Fintype n] {R : Type v} [CommRing R]

variable {S : Type*} [CommRing S]

theorem isCoprime_col (A : SL(2, R)) (j : Fin 2) : IsCoprime (A 0 j) (A 1 j) := by
  refine match j with
  | 0 => ⟨A 1 1, -(A 0 1), ?_⟩
  | 1 => ⟨-(A 1 0), A 0 0, ?_⟩ <;>
  · simp_rw [Matrix.SpecialLinearGroup.det_coe A ▸ det_fin_two A.1]
    ring

