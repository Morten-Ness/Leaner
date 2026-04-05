import Mathlib

open scoped Pointwise

variable {G H α : Type*}

variable [Group G] [Group H] [MulAction G α] {a : G} {s t : Set α}

theorem stabilizer_inf_stabilizer_le_stabilizer_apply₂ {f : Set α → Set α → Set α}
    (hf : ∀ a : G, a • f s t = f (a • s) (a • t)) :
    stabilizer G s ⊓ stabilizer G t ≤ stabilizer G (f s t) := by aesop (add simp [SetLike.le_def])

