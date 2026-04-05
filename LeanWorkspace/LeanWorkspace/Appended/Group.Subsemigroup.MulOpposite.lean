import Mathlib

section

variable {ι : Sort*} {M : Type*} [Mul M]

theorem op_eq_bot {S : Subsemigroup M} : S.op = ⊥ ↔ S = ⊥ := Subsemigroup.op_injective.eq_iff' Subsemigroup.op_bot

end

section

variable {ι : Sort*} {M : Type*} [Mul M]

theorem op_eq_top {S : Subsemigroup M} : S.op = ⊤ ↔ S = ⊤ := Subsemigroup.op_injective.eq_iff' Subsemigroup.op_top

end

section

variable {ι : Sort*} {M : Type*} [Mul M]

theorem op_sInf (S : Set (Subsemigroup M)) : (sInf S).op = sInf (.unop ⁻¹' S) := Subsemigroup.opEquiv.map_sInf_eq_sInf_symm_preimage _

end

section

variable {ι : Sort*} {M : Type*} [Mul M]

theorem op_sSup (S : Set (Subsemigroup M)) : (sSup S).op = sSup (.unop ⁻¹' S) := Subsemigroup.opEquiv.map_sSup_eq_sSup_symm_preimage _

end

section

variable {ι : Sort*} {M : Type*} [Mul M]

theorem unop_eq_bot {S : Subsemigroup Mᵐᵒᵖ} : S.unop = ⊥ ↔ S = ⊥ := Subsemigroup.unop_injective.eq_iff' Subsemigroup.unop_bot

end

section

variable {ι : Sort*} {M : Type*} [Mul M]

theorem unop_eq_top {S : Subsemigroup Mᵐᵒᵖ} : S.unop = ⊤ ↔ S = ⊤ := Subsemigroup.unop_injective.eq_iff' Subsemigroup.unop_top

end

section

variable {ι : Sort*} {M : Type*} [Mul M]

theorem unop_iInf (S : ι → Subsemigroup Mᵐᵒᵖ) : (iInf S).unop = ⨅ i, (S i).unop := Subsemigroup.opEquiv.symm.map_iInf _

end

section

variable {ι : Sort*} {M : Type*} [Mul M]

theorem unop_iSup (S : ι → Subsemigroup Mᵐᵒᵖ) : (iSup S).unop = ⨆ i, (S i).unop := Subsemigroup.opEquiv.symm.map_iSup _

end

section

variable {ι : Sort*} {M : Type*} [Mul M]

theorem unop_inj {S T : Subsemigroup Mᵐᵒᵖ} : S.unop = T.unop ↔ S = T := Subsemigroup.opEquiv.symm.eq_iff_eq

end

section

variable {ι : Sort*} {M : Type*} [Mul M]

theorem unop_injective : (@Subsemigroup.unop M _).Injective := Subsemigroup.opEquiv.symm.injective

end

section

variable {ι : Sort*} {M : Type*} [Mul M]

theorem unop_sInf (S : Set (Subsemigroup Mᵐᵒᵖ)) : (sInf S).unop = sInf (.op ⁻¹' S) := Subsemigroup.opEquiv.symm.map_sInf_eq_sInf_symm_preimage _

end

section

variable {ι : Sort*} {M : Type*} [Mul M]

theorem unop_sSup (S : Set (Subsemigroup Mᵐᵒᵖ)) : (sSup S).unop = sSup (.op ⁻¹' S) := Subsemigroup.opEquiv.symm.map_sSup_eq_sSup_symm_preimage _

end

section

variable {ι : Sort*} {M : Type*} [Mul M]

theorem unop_sup (S₁ S₂ : Subsemigroup Mᵐᵒᵖ) : (S₁ ⊔ S₂).unop = S₁.unop ⊔ S₂.unop := Subsemigroup.opEquiv.symm.map_sup _ _

end
