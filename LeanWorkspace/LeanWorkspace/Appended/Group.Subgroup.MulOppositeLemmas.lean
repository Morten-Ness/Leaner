import Mathlib

section

variable {ι : Sort*} {G : Type*} [Group G]

theorem normal_op {H : Subgroup G} : H.op.Normal ↔ H.Normal := by
  simp only [← normalizer_eq_top_iff, ← op_normalizer, Subgroup.op_eq_top]

end

section

variable {ι : Sort*} {G : Type*} [Group G]

theorem normal_unop {H : Subgroup Gᵐᵒᵖ} : H.unop.Normal ↔ H.Normal := by
  rw [← Subgroup.normal_op, op_unop]

end

section

variable {ι : Sort*} {G : Type*} [Group G]

theorem op_closure (s : Set G) : (closure s).op = closure (MulOpposite.unop ⁻¹' s) := by
  simp_rw [closure, Subgroup.op_sInf, Set.preimage_setOf_eq, Subgroup.coe_unop]
  congr with a
  exact MulOpposite.unop_surjective.forall

end

section

variable {ι : Sort*} {G : Type*} [Group G]

theorem op_eq_bot {S : Subgroup G} : S.op = ⊥ ↔ S = ⊥ := op_injective.eq_iff' Subgroup.op_bot

end

section

variable {ι : Sort*} {G : Type*} [Group G]

theorem op_eq_top {S : Subgroup G} : S.op = ⊤ ↔ S = ⊤ := op_injective.eq_iff' Subgroup.op_top

end

section

variable {ι : Sort*} {G : Type*} [Group G]

theorem op_sInf (S : Set (Subgroup G)) : (sInf S).op = sInf (.unop ⁻¹' S) := opEquiv.map_sInf_eq_sInf_symm_preimage _

end

section

variable {ι : Sort*} {G : Type*} [Group G]

theorem op_sSup (S : Set (Subgroup G)) : (sSup S).op = sSup (.unop ⁻¹' S) := opEquiv.map_sSup_eq_sSup_symm_preimage _

end

section

variable {ι : Sort*} {G : Type*} [Group G]

theorem unop_closure (s : Set Gᵐᵒᵖ) : (closure s).unop = closure (MulOpposite.op ⁻¹' s) := by
  rw [← op_inj, op_unop, Subgroup.op_closure]
  simp_rw [Set.preimage_preimage, MulOpposite.op_unop, Set.preimage_id']

end

section

variable {ι : Sort*} {G : Type*} [Group G]

theorem unop_eq_bot {S : Subgroup Gᵐᵒᵖ} : S.unop = ⊥ ↔ S = ⊥ := unop_injective.eq_iff' Subgroup.unop_bot

end

section

variable {ι : Sort*} {G : Type*} [Group G]

theorem unop_eq_top {S : Subgroup Gᵐᵒᵖ} : S.unop = ⊤ ↔ S = ⊤ := unop_injective.eq_iff' Subgroup.unop_top

end

section

variable {ι : Sort*} {G : Type*} [Group G]

theorem unop_sInf (S : Set (Subgroup Gᵐᵒᵖ)) : (sInf S).unop = sInf (.op ⁻¹' S) := opEquiv.symm.map_sInf_eq_sInf_symm_preimage _

end

section

variable {ι : Sort*} {G : Type*} [Group G]

theorem unop_sSup (S : Set (Subgroup Gᵐᵒᵖ)) : (sSup S).unop = sSup (.op ⁻¹' S) := opEquiv.symm.map_sSup_eq_sSup_symm_preimage _

end
