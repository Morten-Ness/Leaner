import Mathlib

section

open scoped AddConstMap

variable {G H K : Type*} [Add G] [Add H] [Add K] {a : G} {b : H} {c : K}

theorem self_trans_symm (e : G ≃+c[a, b] H) : e.trans e.symm = .refl a := AddConstEquiv.toEquiv_injective e.toEquiv.self_trans_symm

end

section

open scoped AddConstMap

variable {G H K : Type*} [Add G] [Add H] [Add K] {a : G} {b : H} {c : K}

theorem symm_trans_self (e : G ≃+c[a, b] H) : e.symm.trans e = .refl b := AddConstEquiv.toEquiv_injective e.toEquiv.symm_trans_self

end

section

open scoped AddConstMap

variable {G H K : Type*} [Add G] [Add H] [Add K] {a : G} {b : H} {c : K}

theorem toEquiv_inj {e₁ e₂ : G ≃+c[a, b] H} : e₁.toEquiv = e₂.toEquiv ↔ e₁ = e₂ := AddConstEquiv.toEquiv_injective.eq_iff

end
