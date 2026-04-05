import Mathlib

variable {S R : Type*} [Semiring R] [StarMul R]
  [SMul S R] [IsScalarTower S R R] [SMulCommClass S R R]

theorem conjStarAlgAut_ext_iff {S : Type*} [CommSemiring S] [Algebra S R] [Algebra.IsCentral S R]
    (u v : unitary R) : Unitary.conjStarAlgAut S R u = Unitary.conjStarAlgAut S R v ↔ ∃ α : S, (u : R) = α • v := by
  conv_lhs => rw [eq_comm]
  simp_rw [StarAlgEquiv.ext_iff, conjStarAlgAut_apply, ← coe_star, star_eq_inv,
    ← val_inv_toUnits_apply, ← val_toUnits_apply, mul_assoc, ← Units.eq_inv_mul_iff_mul_eq,
    ← mul_assoc, Units.eq_mul_inv_iff_mul_eq, mul_assoc, ← mul_assoc (((toUnits v)⁻¹ : Rˣ) : R),
    ← Subalgebra.mem_center_iff (R := S), Algebra.IsCentral.center_eq_bot, Algebra.mem_bot,
    Set.mem_range, Algebra.algebraMap_eq_smul_one, Units.eq_inv_mul_iff_mul_eq, mul_smul_comm,
    mul_one, eq_comm]

