import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [VSub α β] {s t : Set β}

theorem toFinset_vsub (s t : Set β) [Fintype s] [Fintype t] [Fintype ↑(s -ᵥ t)] :
    (s -ᵥ t : Set α).toFinset = s.toFinset -ᵥ t.toFinset := toFinset_image2 _ _ _

