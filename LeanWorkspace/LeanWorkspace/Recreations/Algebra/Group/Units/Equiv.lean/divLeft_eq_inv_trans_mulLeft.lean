import Mathlib

variable {F α M N G : Type*}

variable [Group G]

theorem divLeft_eq_inv_trans_mulLeft (a : G) :
    Equiv.divLeft a = (Equiv.inv G).trans (Equiv.mulLeft a) := ext fun _ => div_eq_mul_inv _ _

