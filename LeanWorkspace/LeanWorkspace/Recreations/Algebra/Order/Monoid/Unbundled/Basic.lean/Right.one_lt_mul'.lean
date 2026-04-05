import Mathlib

variable {α β : Type*}

variable [MulOneClass α]

variable [Preorder α]

theorem Right.one_lt_mul' [MulRightMono α] {a b : α} (ha : 1 < a)
    (hb : 1 < b) :
    1 < a * b := lt_mul_of_one_lt_of_lt' ha hb

alias mul_le_one' := Left.mul_le_one

alias mul_lt_one_of_le_of_lt := Left.mul_lt_one_of_le_of_lt

alias mul_lt_one_of_lt_of_le := Left.mul_lt_one_of_lt_of_le

alias mul_lt_one := Left.mul_lt_one

alias mul_lt_one' := Left.mul_lt_one'

attribute [to_additive add_nonpos /-- **Alias** of `Left.add_nonpos`. -/] mul_le_one'

attribute [to_additive add_neg_of_nonpos_of_neg

