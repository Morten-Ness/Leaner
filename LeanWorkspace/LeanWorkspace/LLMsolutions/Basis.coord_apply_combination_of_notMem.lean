FAIL
import Mathlib

variable {ι ι' G G' k V P : Type*} [AddCommGroup V] [AddTorsor V P]

variable [Ring k] [Module k V] (b : AffineBasis ι k P) {s : Finset ι} {i j : ι} (e : ι ≃ ι')

theorem coord_apply_combination_of_notMem (hi : i ∉ s) {w : ι → k} (hw : s.sum w = 1) :
    b.coord i (s.affineCombination k b w) = 0 := by
  classical
  let p := s.affineCombination k b w
  have hp : p = s.affineCombination k b w := rfl
  have hsum :
      ∑ j in s, w j • (b j :ᵥ p) = 0 := by
    rw [← Finset.weightedVSub_eq_weightedVSubOfPoint_vsub hw p]
    simp [p, Finset.affineCombination_vsub hw]
  have hrepr := congrArg (b.basis.repr) hsum
  simp only [LinearEquiv.map_sum, map_smul, Basis.repr_self, Pi.smul_apply, smul_eq_mul,
    Finsupp.sum, Finset.sum_apply] at hrepr
  have := congrArg (fun f => f i) hrepr
  simp only [Pi.zero_apply] at this
  rw [show b.coord i p = (b.basis.repr (b i :ᵥ p)) i by rfl]
  rw [show (b i :ᵥ p) = - (p :ᵥ b i) by simpa using vsub_rev p (b i)]
  rw [b.basis.repr_neg]
  have hcoeff : (b.basis.repr (p :ᵥ b i)) i = 0 := by
    have hrepr' : b.basis.repr (p :ᵥ b i) = ∑ j in s, w j • b.basis.repr (p :ᵥ b j) := by
      simpa [p] using congrArg (b.basis.repr) (Finset.affineCombination_vsub hw (b := b) (s := s) (w := w) (p := b i))
    have hi' : ∀ j ∈ s, j ≠ i := by
      intro j hj
      exact fun h => hi (h ▸ hj)
    have hzero :
        (∑ j in s, w j • b.basis.repr (p :ᵥ b j)) i = 0 := by
      refine Finset.sum_eq_zero ?_
      intro j hj
      simp [AffineBasis.basis_repr, hi' j hj]
    have := congrArg (fun f => f i) hrepr'
    simpa [hzero] using this
  simp [hcoeff]
