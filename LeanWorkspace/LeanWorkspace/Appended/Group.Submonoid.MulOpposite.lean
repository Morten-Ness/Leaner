import Mathlib

section

variable {ι : Sort*} {M : Type*} [MulOneClass M]

theorem op_eq_bot {S : Submonoid M} : S.op = ⊥ ↔ S = ⊥ := Submonoid.op_injective.eq_iff' Submonoid.op_bot

end

section

variable {ι : Sort*} {M : Type*} [MulOneClass M]

theorem op_eq_top {S : Submonoid M} : S.op = ⊤ ↔ S = ⊤ := Submonoid.op_injective.eq_iff' Submonoid.op_top

end

section

variable {ι : Sort*} {M : Type*} [MulOneClass M]

theorem op_sInf (S : Set (Submonoid M)) : (sInf S).op = sInf (.unop ⁻¹' S) := Submonoid.opEquiv.map_sInf_eq_sInf_symm_preimage _

end

section

variable {ι : Sort*} {M : Type*} [MulOneClass M]

theorem op_sSup (S : Set (Submonoid M)) : (sSup S).op = sSup (.unop ⁻¹' S) := Submonoid.opEquiv.map_sSup_eq_sSup_symm_preimage _

end

section

variable {ι : Sort*} {M : Type*} [MulOneClass M]

theorem unop_eq_bot {S : Submonoid Mᵐᵒᵖ} : S.unop = ⊥ ↔ S = ⊥ := Submonoid.unop_injective.eq_iff' Submonoid.unop_bot

end

section

variable {ι : Sort*} {M : Type*} [MulOneClass M]

theorem unop_eq_top {S : Submonoid Mᵐᵒᵖ} : S.unop = ⊤ ↔ S = ⊤ := Submonoid.unop_injective.eq_iff' Submonoid.unop_top

end

section

variable {ι : Sort*} {M : Type*} [MulOneClass M]

theorem unop_sInf (S : Set (Submonoid Mᵐᵒᵖ)) : (sInf S).unop = sInf (.op ⁻¹' S) := Submonoid.opEquiv.symm.map_sInf_eq_sInf_symm_preimage _

end

section

variable {ι : Sort*} {M : Type*} [MulOneClass M]

theorem unop_sSup (S : Set (Submonoid Mᵐᵒᵖ)) : (sSup S).unop = sSup (.op ⁻¹' S) := Submonoid.opEquiv.symm.map_sSup_eq_sSup_symm_preimage _

end
