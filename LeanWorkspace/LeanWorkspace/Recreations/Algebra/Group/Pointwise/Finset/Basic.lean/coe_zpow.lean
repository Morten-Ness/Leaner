import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [DecidableEq β]

variable [DivisionMonoid α] {s t : Finset α} {n : ℤ}

theorem coe_zpow (s : Finset α) : ∀ n : ℤ, ↑(s ^ n) = (s : Set α) ^ n
  | Int.ofNat _ => Finset.coe_pow _ _
  | Int.negSucc n => by
    refine (Finset.coe_inv _).trans ?_
    exact congr_arg Inv.inv (Finset.coe_pow _ _)
