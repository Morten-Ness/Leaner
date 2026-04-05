import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [Mul α] [IsLeftCancelMul α] {s t : Set α}

theorem pairwiseDisjoint_smul_iff :
    s.PairwiseDisjoint (· • t) ↔ (s ×ˢ t).InjOn fun p ↦ p.1 * p.2 := pairwiseDisjoint_image_right_iff fun _ _ ↦ mul_right_injective _

