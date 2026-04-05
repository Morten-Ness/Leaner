import Mathlib

variable (α β : Type*)

variable {α β} {a a₁ a₂ : α} {b b₁ b₂ : β}

variable [SMul α β]

variable [Preorder α] [Preorder β]

variable [Zero β]

theorem lt_of_smul_lt_smul_right [SMulPosReflectLT α β] (h : a₁ • b < a₂ • b) (hb : 0 ≤ b) :
    a₁ < a₂ := SMulPosReflectLT.lt_of_smul_lt_smul_right hb h

