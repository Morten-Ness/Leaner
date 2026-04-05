import Mathlib

open scoped Function

variable (R : Type*)

variable [Ring R] (S : Sequence R)

variable [IsDomain R]

variable (hCoeff : ∀ i, IsUnit (S i).leadingCoeff)

theorem basis_eq_self (i : ℕ) : S.basis hCoeff i = S i := Module.Basis.mk_apply _ _ _

