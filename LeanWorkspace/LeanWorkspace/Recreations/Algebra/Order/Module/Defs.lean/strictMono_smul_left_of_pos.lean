import Mathlib

variable (α β : Type*)

variable {α β} {a a₁ a₂ : α} {b b₁ b₂ : β}

variable [SMul α β]

variable [Preorder α] [Preorder β]

variable [Zero α]

theorem strictMono_smul_left_of_pos [PosSMulStrictMono α β] (ha : 0 < a) :
    StrictMono ((a • ·) : β → β) := PosSMulStrictMono.smul_lt_smul_of_pos_left ha

