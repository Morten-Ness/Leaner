import Mathlib

open scoped DirectSum

variable {R : Type u} [CommRing R] [IsPrincipalIdealRing R]

variable {M : Type v} [AddCommGroup M] [Module R M]

variable [IsDomain R]

set_option backward.isDefEq.respectTransparency false in
theorem exists_ker_toSpanSingleton_eq_annihilator [Module.Finite R M] :
    ∃ x : M, ker (toSpanSingleton R _ x) = annihilator R M := by
  have ⟨m, ι, _, p, irr, n, ⟨e⟩⟩ := Module.equiv_free_prod_directSum (R := R) (M := M)
  refine ⟨e.symm (Finsupp.equivFunOnFinite.symm fun _ ↦ 1, DFinsupp.equivFunOnFintype.symm
    fun _ ↦ mkQ _ 1), le_antisymm (fun x h ↦ ?_) fun x h ↦ mem_annihilator.mp h _⟩
  rw [mem_ker, toSpanSingleton_apply, ← map_smul,
    e.symm.map_eq_zero_iff, Prod.ext_iff, Finsupp.ext_iff, DFinsupp.ext_iff] at h
  obtain _ | m := m
  · rw [← mul_one x, ← smul_eq_mul, e.annihilator_eq, annihilator_prod]
    simp_rw [annihilator_eq_top_iff.mpr inferInstance, DirectSum, annihilator_dfinsupp,
      top_inf_eq, mem_iInf, Ideal.annihilator_quotient, ← Quotient.mk_eq_zero]
    exact h.2
  · rw [show x = 0 by simpa using h.1 0]
    exact zero_mem _

