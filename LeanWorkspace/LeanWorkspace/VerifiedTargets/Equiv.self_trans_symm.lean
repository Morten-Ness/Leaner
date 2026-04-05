import Mathlib

open scoped AddConstMap

variable {G H K : Type*} [Add G] [Add H] [Add K] {a : G} {b : H} {c : K}

theorem self_trans_symm (e : G ≃+c[a, b] H) : e.trans e.symm = .refl a := AddConstEquiv.toEquiv_injective e.toEquiv.self_trans_symm

