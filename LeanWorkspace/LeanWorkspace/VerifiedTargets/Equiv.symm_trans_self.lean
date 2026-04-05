import Mathlib

open scoped AddConstMap

variable {G H K : Type*} [Add G] [Add H] [Add K] {a : G} {b : H} {c : K}

theorem symm_trans_self (e : G ≃+c[a, b] H) : e.symm.trans e = .refl b := AddConstEquiv.toEquiv_injective e.toEquiv.symm_trans_self

