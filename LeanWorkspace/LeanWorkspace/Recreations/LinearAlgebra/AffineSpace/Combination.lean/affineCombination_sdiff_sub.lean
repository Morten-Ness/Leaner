import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

variable (k)

variable {k}

theorem affineCombination_sdiff_sub [DecidableEq ι] {s₂ : Finset ι} (h : s₂ ⊆ s) (w : ι → k)
    (p : ι → P) :
    (s \ s₂).affineCombination k p w -ᵥ s₂.affineCombination k p (-w) = s.weightedVSub p w := by
  simp_rw [Finset.affineCombination_apply, vadd_vsub_vadd_cancel_right]
  exact Finset.weightedVSub_sdiff_sub s h _ _

