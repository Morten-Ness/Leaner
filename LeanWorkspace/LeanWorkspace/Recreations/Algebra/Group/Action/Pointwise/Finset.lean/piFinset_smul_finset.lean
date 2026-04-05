import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable {ι : Type*} {α β : ι → Type*} [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (β i)]

theorem piFinset_smul_finset [∀ i, SMul (α i) (β i)] (a : ∀ i, α i) (s : ∀ i, Finset (β i)) :
    piFinset (fun i ↦ a i • s i) = a • piFinset s := piFinset_image _ _

-- Note: We don't currently state `piFinset_vsub` because there's no
-- `[∀ i, VSub (β i) (α i)] → VSub (∀ i, β i) (∀ i, α i)` instance

