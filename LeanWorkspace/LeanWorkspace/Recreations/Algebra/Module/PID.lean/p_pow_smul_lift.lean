import Mathlib

open scoped DirectSum

variable {R : Type u} [CommRing R] [IsPrincipalIdealRing R]

variable {M : Type v} [AddCommGroup M] [Module R M]

variable [IsDomain R]

variable {p : R} (hp : Irreducible p) (hM : Module.IsTorsion' M (Submonoid.powers p))

variable [dec : ∀ x : M, Decidable (x = 0)]

theorem p_pow_smul_lift {x y : M} {k : ℕ} (hM' : Module.IsTorsionBy R M (p ^ pOrder hM y))
    (h : p ^ k • x ∈ R ∙ y) : ∃ a : R, p ^ k • x = p ^ k • a • y := by
  by_cases! hk : k ≤ pOrder hM y
  · let f :=
      ((R ∙ p ^ (pOrder hM y - k) * p ^ k).quotEquivOfEq _ ?_).trans
        (quotTorsionOfEquivSpanSingleton R M y)
    · have : f.symm ⟨p ^ k • x, h⟩ ∈
          R ∙ Ideal.Quotient.mk (R ∙ p ^ (pOrder hM y - k) * p ^ k) (p ^ k) := by
        rw [← Quotient.torsionBy_eq_span_singleton, mem_torsionBy_iff, ← f.symm.map_smul]
        · convert f.symm.map_zero; ext
          rw [coe_smul_of_tower, coe_mk, coe_zero, smul_smul, ← pow_add, Nat.sub_add_cancel hk,
            @hM' x]
        · exact mem_nonZeroDivisors_of_ne_zero (pow_ne_zero _ hp.ne_zero)
      rw [Submodule.mem_span_singleton] at this; obtain ⟨a, ha⟩ := this; use a
      rw [f.eq_symm_apply, ← Ideal.Quotient.mk_eq_mk, ← Quotient.mk_smul] at ha
      dsimp only [smul_eq_mul, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk,
        quotTorsionOfEquivSpanSingleton_apply_mk] at ha
      rw [smul_smul, mul_comm]; exact congr_arg ((↑) : _ → M) ha.symm
    · symm; convert Ideal.torsionOf_eq_span_pow_pOrder hp hM y
      rw [← pow_add, Nat.sub_add_cancel hk]
  · use 0
    rw [zero_smul, smul_zero, ← Nat.sub_add_cancel hk.le, pow_add, mul_smul, hM',
      smul_zero]

