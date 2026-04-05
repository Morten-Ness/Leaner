import Mathlib

variable {ι κ α β R M : Type*}

variable [DecidableEq ι] [Fintype ι] [AddCommMonoid α]

theorem sum_piFinset_apply (f : κ → α) (s : Finset κ) (i : ι) :
    ∑ g ∈ piFinset fun _ : ι ↦ s, f (g i) = #s ^ (card ι - 1) • ∑ b ∈ s, f b := by
  classical
  rw [Finset.sum_comp]
  simp only [eval_image_piFinset_const, card_filter_piFinset_const s, ite_smul, zero_smul, smul_sum,
    Finset.sum_ite_mem, inter_self]

