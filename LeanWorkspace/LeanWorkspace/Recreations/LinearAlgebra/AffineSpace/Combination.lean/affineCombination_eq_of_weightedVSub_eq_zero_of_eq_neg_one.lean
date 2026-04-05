import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

variable (k)

variable {k}

theorem affineCombination_eq_of_weightedVSub_eq_zero_of_eq_neg_one {w : ι → k} {p : ι → P}
    (hw : s.weightedVSub p w = (0 : V)) {i : ι} [DecidablePred (· ≠ i)] (his : i ∈ s)
    (hwi : w i = -1) : {x ∈ s | x ≠ i}.affineCombination k p w = p i := by
  classical
    rw [← @vsub_eq_zero_iff_eq V, ← hw,
      ← Finset.affineCombination_sdiff_sub s (singleton_subset_iff.2 his), sdiff_singleton_eq_erase,
      ← filter_ne']
    congr
    refine (Finset.affineCombination_of_eq_one_of_eq_zero _ _ _ (mem_singleton_self _) ?_ ?_).symm
    · simp [hwi]
    · simp

