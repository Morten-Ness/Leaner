import Mathlib

open scoped AddConstMap

variable {G H K : Type*} [Add G] [Add H] [Add K] {a : G} {b : H} {c : K}

theorem symm_trans_self (e : G ≃+c[a, b] H) : e.symm.trans e = .refl b := by
  ext x
  exact e.apply_symm_apply x
