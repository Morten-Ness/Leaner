FAIL
import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

theorem weightedVSub_smul {G : Type*} [Group G] [DistribMulAction G V] [SMulCommClass G k V]
    {s : Finset ι} {w : ι → k} (h : ∑ i ∈ s, w i = 0) (p : ι → V) (a : G) :
    s.weightedVSub (a • p) w = a • s.weightedVSub p w := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp at h
      simp [Finset.weightedVSub]
  | @insert i s hi hs =>
      rw [Finset.sum_insert hi] at h
      rw [Finset.weightedVSub_insert hi, Finset.weightedVSub_insert hi]
      simp only [Pi.smul_apply]
      rw [hs (by simpa [h])]
      calc
        w i • ((a • p i) -ᵥ (a • p i)) + a • s.weightedVSub p w = a • s.weightedVSub p w := by
          simp
        _ = a • (w i • (p i -ᵥ p i) + s.weightedVSub p w) := by
          simp
      · exact h
      · simp [h]
