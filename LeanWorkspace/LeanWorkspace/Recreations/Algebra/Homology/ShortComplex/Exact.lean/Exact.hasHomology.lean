import Mathlib

variable {C D : Type*} [Category* C] [Category* D]

theorem Exact.hasHomology (h : S.Exact) : S.HasHomology := HasHomology.mk' h.condition.choose

