import Mathlib

variable {α : Type*} [Preorder α] [OrderBot α] [AddMonoidWithOne α] [SuccAddOrder α]

theorem succ_ofNat (n : ℕ) [n.AtLeastTwo] :
    succ (ofNat(n) : WithBot α) = ofNat(n) + 1 := WithBot.succ_natCast n

