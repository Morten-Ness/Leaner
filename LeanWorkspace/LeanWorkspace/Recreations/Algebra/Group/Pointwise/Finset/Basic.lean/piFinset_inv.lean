import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable {ι : Type*} {α β : ι → Type*} [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (β i)]
  [∀ i, DecidableEq (α i)]

theorem piFinset_inv [∀ i, Inv (α i)] (s : ∀ i, Finset (α i)) :
    piFinset (fun i ↦ (s i)⁻¹) = (piFinset s)⁻¹ := piFinset_image _ _

