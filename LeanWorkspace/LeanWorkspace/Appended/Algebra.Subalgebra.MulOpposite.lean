import Mathlib

section

variable {ι : Sort*} {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

theorem op_sInf (S : Set (Subalgebra R A)) : (sInf S).op = sInf (.unop ⁻¹' S) := Subalgebra.opEquiv.map_sInf_eq_sInf_symm_preimage _

end

section

variable {ι : Sort*} {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

theorem op_sSup (S : Set (Subalgebra R A)) : (sSup S).op = sSup (.unop ⁻¹' S) := Subalgebra.opEquiv.map_sSup_eq_sSup_symm_preimage _

end

section

variable {ι : Sort*} {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

theorem unop_inf (S₁ S₂ : Subalgebra R Aᵐᵒᵖ) : (S₁ ⊓ S₂).unop = S₁.unop ⊓ S₂.unop := Subalgebra.opEquiv.symm.map_inf _ _

end

section

variable {ι : Sort*} {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

theorem unop_sInf (S : Set (Subalgebra R Aᵐᵒᵖ)) : (sInf S).unop = sInf (.op ⁻¹' S) := Subalgebra.opEquiv.symm.map_sInf_eq_sInf_symm_preimage _

end

section

variable {ι : Sort*} {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

theorem unop_sSup (S : Set (Subalgebra R Aᵐᵒᵖ)) : (sSup S).unop = sSup (.op ⁻¹' S) := Subalgebra.opEquiv.symm.map_sSup_eq_sSup_symm_preimage _

end

section

variable {ι : Sort*} {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

theorem unop_sup (S₁ S₂ : Subalgebra R Aᵐᵒᵖ) : (S₁ ⊔ S₂).unop = S₁.unop ⊔ S₂.unop := Subalgebra.opEquiv.symm.map_sup _ _

end
