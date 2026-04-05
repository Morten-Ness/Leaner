import Mathlib

variable {α : Type*}

variable [AddMonoid α] [Preorder α] [AddLeftMono α]

theorem nsmul_coe (n : ℕ) (r : { x : α // 0 ≤ x }) :
    ↑(n • r) = n • (r : α) := Nonneg.coeAddMonoidHom.map_nsmul _ _

