import Mathlib

open scoped Cardinal Pointwise

variable {G M α : Type*}

variable [Group G] {s t : Set G}

variable [MulAction G α]

theorem natCard_smul_set (a : G) (s : Set α) : Nat.card ↥(a • s) = Nat.card s := by
  simp

