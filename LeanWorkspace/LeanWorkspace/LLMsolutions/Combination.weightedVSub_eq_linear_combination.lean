FAIL
import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

variable (k)

variable {k}

theorem weightedVSub_eq_linear_combination {ι} (s : Finset ι) {w : ι → k} {p : ι → V}
    (hw : s.sum w = 0) : s.weightedVSub p w = ∑ i ∈ s, w i • p i := by
  classical
  unfold Finset.weightedVSub
  by_cases hs : s.Nonempty
  · obtain ⟨i, hi⟩ := hs
    rw [show (Classical.choose hs : ι) = i by
      apply Finset.mem_coe.1
      exact Classical.choose_spec hs]
    have hsub : ∀ j, p j -ᵥ p i = p j - p i := by
      intro j
      simp
    simp_rw [hsub]
    rw [Finset.sum_sub_distrib]
    rw [Finset.sum_congr rfl fun j hj => smul_sub]
    rw [← Finset.sum_mul]
    simp [hw]
  · simp [hs] at hw
    simp [Finset.not_nonempty_iff_eq_empty.mp hs]
