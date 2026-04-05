import Mathlib

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable {H : LieSubalgebra R L} (α χ : H → R) (p q : ℤ)

variable [H.IsCartanSubalgebra] [IsNoetherian R L]

set_option backward.isDefEq.respectTransparency false in
theorem trace_toEnd_genWeightSpaceChain_eq_zero
    (hp : genWeightSpace M (p • α + χ) = ⊥)
    (hq : genWeightSpace M (q • α + χ) = ⊥)
    {x : H} (hx : x ∈ corootSpace α) :
    LinearMap.trace R _ (toEnd R H (LieModule.genWeightSpaceChain M α χ p q) x) = 0 := by
  rw [LieAlgebra.mem_corootSpace'] at hx
  induction hx using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨y, hy, z, hz, hyz⟩ := hu
    let f : Module.End R (LieModule.genWeightSpaceChain M α χ p q) :=
      { toFun := fun ⟨m, hm⟩ ↦ ⟨⁅(y : L), m⁆,
          LieModule.lie_mem_genWeightSpaceChain_of_genWeightSpace_eq_bot_right M α χ p q hq hy hm⟩
        map_add' := fun _ _ ↦ by simp
        map_smul' := fun t m ↦ by simp }
    let g : Module.End R (LieModule.genWeightSpaceChain M α χ p q) :=
      { toFun := fun ⟨m, hm⟩ ↦ ⟨⁅(z : L), m⁆,
          LieModule.lie_mem_genWeightSpaceChain_of_genWeightSpace_eq_bot_left M α χ p q hp hz hm⟩
        map_add' := fun _ _ ↦ by simp
        map_smul' := fun t m ↦ by simp }
    have hfg : toEnd R H _ u = ⁅f, g⁆ := by
      ext
      rw [toEnd_apply_apply, LieSubmodule.coe_bracket, LieSubalgebra.coe_bracket_of_module, ← hyz]
      simp only [lie_lie, LieHom.lie_apply, LinearMap.coe_mk, AddHom.coe_mk, Module.End.lie_apply,
        AddSubgroupClass.coe_sub, f, g]
    simp [hfg]
  | zero => simp
  | add => simp_all
  | smul => simp_all

