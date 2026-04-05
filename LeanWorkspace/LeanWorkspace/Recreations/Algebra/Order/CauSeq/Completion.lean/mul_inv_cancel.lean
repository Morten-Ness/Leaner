import Mathlib

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

variable {β : Type*} [DivisionRing β] {abv : β → α} [IsAbsoluteValue abv]

theorem mul_inv_cancel {x : (CauSeq.Completion.Cauchy abv)} : x ≠ 0 → x * x⁻¹ = 1 := Quotient.inductionOn x fun f hf => by
    simp only [CauSeq.Completion.mk_eq_mk, ne_eq, CauSeq.Completion.mk_eq_zero] at hf
    simp only [CauSeq.Completion.mk_eq_mk, hf, not_false_eq_true, CauSeq.Completion.inv_mk, CauSeq.Completion.mk_mul]
    exact Quotient.sound (CauSeq.mul_inv_cancel hf)

