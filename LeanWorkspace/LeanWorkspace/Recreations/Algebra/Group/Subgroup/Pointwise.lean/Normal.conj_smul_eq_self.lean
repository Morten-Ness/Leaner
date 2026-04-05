import Mathlib

variable {α G A S : Type*}

variable [Group G] [AddGroup A] {s : Set G}

variable [Group α] [MulDistribMulAction α G]

theorem Normal.conj_smul_eq_self (g : G) (H : Subgroup G) [h : Normal H] : MulAut.conj g • H = H := h.conjAct g

