import Mathlib

variable {S R : Type*} [Semiring R] [StarMul R]
  [SMul S R] [IsScalarTower S R R] [SMulCommClass S R R]

theorem conjStarAlgAut_ext_iff' {R S : Type*} [Ring R] [StarMul R] [CommRing S] [StarMul S]
    [Algebra S R] [StarModule S R] [Algebra.IsCentral S R] [IsCancelMulZero S]
    [Module.IsTorsionFree S R] (u v : unitary R) :
    Unitary.conjStarAlgAut S R u = Unitary.conjStarAlgAut S R v ↔ ∃ α : unitary S, u = α • v := by
  conv_lhs => rw [eq_comm]
  simp_rw [StarAlgEquiv.ext_iff, conjStarAlgAut_apply, ← coe_star, star_eq_inv,
    ← val_inv_toUnits_apply, ← val_toUnits_apply, mul_assoc, ← Units.eq_inv_mul_iff_mul_eq,
    ← mul_assoc, Units.eq_mul_inv_iff_mul_eq, mul_assoc, ← mul_assoc (((toUnits v)⁻¹ : Rˣ) : R),
    ← Subalgebra.mem_center_iff (R := S), Algebra.IsCentral.center_eq_bot, Algebra.mem_bot,
    Set.mem_range, Algebra.algebraMap_eq_smul_one, val_inv_toUnits_apply, val_toUnits_apply,
    ← star_eq_inv, coe_star]
  refine ⟨fun ⟨y, h⟩ ↦ ?_, fun ⟨y, h⟩ ↦ ⟨(y : S), by
    simp only [h, coe_smul, mul_smul_comm, SetLike.coe_mem, star_mul_self_of_mem]; rfl⟩⟩
  have huv : (u : R) = y • (v : R) := by simpa [← mul_assoc] using congr(v * $h).symm
  have hvu : (v : R) = star y • (u : R) := by simpa [← mul_assoc] using congr(u * (star $h)).symm
  have hvy : (v : R) = (star y * y) • (v : R) := by simp [← smul_smul, ← huv, ← hvu]
  nth_rw 1 [← one_smul S (v : R)] at hvy
  rw [← sub_eq_zero, ← sub_smul, smul_eq_zero, sub_eq_zero, eq_comm] at hvy
  obtain (this | this) := hvy
  · exact ⟨⟨y, by simp [mem_iff, this, mul_comm y]⟩, by ext; exact huv⟩
  · exact ⟨1, by ext; simp [this, huv] at huv ⊢⟩

