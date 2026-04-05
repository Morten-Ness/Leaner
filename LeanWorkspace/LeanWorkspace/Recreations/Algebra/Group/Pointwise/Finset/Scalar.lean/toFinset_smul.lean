import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [SMul α β] [DecidableEq β] {s : Set α} {t : Set β}

theorem toFinset_smul (s : Set α) (t : Set β) [Fintype s] [Fintype t] [Fintype ↑(s • t)] :
    (s • t).toFinset = s.toFinset • t.toFinset := toFinset_image2 _ _ _

