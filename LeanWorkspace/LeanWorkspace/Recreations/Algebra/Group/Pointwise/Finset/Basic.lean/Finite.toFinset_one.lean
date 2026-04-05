import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [One α]

theorem Finite.toFinset_one (h : (1 : Set α).Finite := finite_one) : h.toFinset = 1 :=
  Finite.toFinset_singleton _

