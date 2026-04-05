import Mathlib

variable (α β : Type*)

variable {α β} {a a₁ a₂ : α} {b b₁ b₂ : β}

variable [SMul α β]

theorem smul_one_strictMono [Preorder α] [PartialOrder β] [Zero β] [One β] [ZeroLEOneClass β]
    [NeZero (1 : β)] [SMulPosStrictMono α β] :
    StrictMono (fun x : α ↦ x • (1 : β)) := fun _ _ ha ↦ smul_lt_smul_of_pos_right ha (zero_lt_one (α := β))

