import Mathlib

open scoped Pointwise

variable {ι α : Type*}

theorem coe_pow_interval [CommMonoid α] [Preorder α] [IsOrderedMonoid α]
    (s : NonemptyInterval α) (n : ℕ) :
    ↑(s ^ n) = (s : Interval α) ^ n := map_pow (⟨⟨(↑), NonemptyInterval.coe_one_interval⟩, NonemptyInterval.coe_mul_interval⟩ : NonemptyInterval α →* Interval α) _ _

-- simp can already prove `coe_nsmul_interval`
attribute [simp] coe_pow_interval

