import Mathlib

variable {R : Type*} [Semiring R]

theorem rankCondition_iff_matrix : RankCondition R ↔ ∀ n m
    (f : Matrix (Fin n) (Fin m) R) (g : Matrix (Fin m) (Fin n) R), g * f = 1 → m ≤ n := by
  simp_rw [rankCondition_iff_le_of_comp_eq_one, ← toLinearMapRight'.toEquiv
    |>.forall_congr_right, LinearEquiv.coe_toEquiv, ← toLinearMapRight'_mul,
    Module.End.one_eq_id, ← toLinearMapRight'_one, toLinearMapRight'.injective.eq_iff]

