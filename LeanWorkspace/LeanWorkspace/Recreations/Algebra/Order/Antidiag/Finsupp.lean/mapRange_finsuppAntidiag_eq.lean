import Mathlib

variable {ι μ μ' : Type*}

variable [DecidableEq ι] [AddCommMonoid μ] [HasAntidiagonal μ] [DecidableEq μ] {s : Finset ι}
  {n : μ} {f : ι →₀ μ}

variable [AddCommMonoid μ'] [HasAntidiagonal μ'] [DecidableEq μ']

theorem mapRange_finsuppAntidiag_eq {e : μ ≃+ μ'} {s : Finset ι} {n : μ} :
    (Finset.finsuppAntidiag s n).map (mapRange.addEquiv e).toEmbedding = Finset.finsuppAntidiag s (e n) := by
  ext f
  constructor
  · apply Finset.mapRange_finsuppAntidiag_subset
  · set h := (mapRange.addEquiv e).toEquiv with hh
    intro hf
    have : n = e.symm (e n) := (AddEquiv.eq_symm_apply e).mpr rfl
    rw [mem_map_equiv, this]
    apply Finset.mapRange_finsuppAntidiag_subset
    rw [← mem_map_equiv]
    convert hf
    rw [map_map, hh]
    convert map_refl
    apply Function.Embedding.equiv_symm_toEmbedding_trans_toEmbedding

