import Mathlib

variable {ι μ μ' : Type*}

variable [DecidableEq ι] [AddCommMonoid μ] [HasAntidiagonal μ] [DecidableEq μ] {s : Finset ι}
  {n : μ} {f : ι →₀ μ}

variable [AddCommMonoid μ'] [HasAntidiagonal μ'] [DecidableEq μ']

theorem mapRange_finsuppAntidiag_subset {e : μ ≃+ μ'} {s : Finset ι} {n : μ} :
    (Finset.finsuppAntidiag s n).map (mapRange.addEquiv e).toEmbedding ⊆ Finset.finsuppAntidiag s (e n) := by
  intro f
  simp only [mem_map, Finset.mem_finsuppAntidiag']
  rintro ⟨g, ⟨hsum, hsupp⟩, rfl⟩
  simp only [AddEquiv.toEquiv_eq_coe, mapRange.addEquiv_toEquiv, Equiv.coe_toEmbedding,
    mapRange.equiv_apply, EquivLike.coe_coe]
  constructor
  · rw [sum_mapRange_index (fun _ ↦ rfl), ← hsum, _root_.map_finsuppSum]
  · exact subset_trans (support_mapRange) hsupp

