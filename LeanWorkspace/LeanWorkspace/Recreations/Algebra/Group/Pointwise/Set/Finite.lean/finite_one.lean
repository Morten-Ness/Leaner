import Mathlib

variable {F α β γ : Type*}

variable [One α]

theorem finite_one : (1 : Set α).Finite := finite_singleton _

