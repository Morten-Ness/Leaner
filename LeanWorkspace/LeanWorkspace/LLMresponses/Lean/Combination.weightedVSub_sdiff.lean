FAIL
import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

theorem weightedVSub_sdiff [DecidableEq ι] {s₂ : Finset ι} (h : s₂ ⊆ s) (w : ι → k) (p : ι → P) :
    (s \ s₂).weightedVSub p w + s₂.weightedVSub p w = s.weightedVSub p w := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have hs₂ : s₂ = ∅ := Finset.eq_empty_of_subset_empty h
      subst hs₂
      simp
  | @insert a s ha ih =>
      by_cases has₂ : a ∈ s₂
      · have hs₂ : s₂ = insert a (s₂.erase a) := by
          exact (Finset.insert_erase has₂).symm
        have hsubset : s₂.erase a ⊆ s := by
          intro x hx
          exact h (Finset.mem_of_mem_erase hx)
        rw [hs₂, Finset.sdiff_insert_insert_eq_sdiff]
        · simp [ha, has₂, ih hsubset, add_assoc]
        · exact h has₂
      · have hsubset : s₂ ⊆ s := by
          intro x hx
          have hx' := h hx
          simp [Finset.mem_insert, hx, has₂] at hx'
          exact hx'
        rw [Finset.sdiff_insert_eq_erase, Finset.erase_eq_of_not_mem has₂]
        · simp [ha, has₂, ih hsubset, add_assoc]
        · intro hs₂sub
          exact has₂ (h hs₂sub)
