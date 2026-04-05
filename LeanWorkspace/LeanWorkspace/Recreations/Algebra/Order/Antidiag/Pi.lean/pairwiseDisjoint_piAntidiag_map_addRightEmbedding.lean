import Mathlib

variable {ι μ μ' : Type*}

variable [DecidableEq ι] [AddCancelCommMonoid μ] [HasAntidiagonal μ] [DecidableEq μ] {i : ι}
  {s : Finset ι}

theorem pairwiseDisjoint_piAntidiag_map_addRightEmbedding (hi : i ∉ s) (n : μ) :
    (antidiagonal n : Set (μ × μ)).PairwiseDisjoint fun p ↦
      map (addRightEmbedding fun j ↦ if j = i then p.1 else 0) (s.piAntidiag p.2) := by
  rintro ⟨a, b⟩ hab ⟨c, d⟩ hcd
  simp only [ne_eq, antidiagonal_congr' hab hcd, disjoint_left, mem_map, mem_piAntidiag,
    addRightEmbedding_apply, not_exists, not_and, and_imp, forall_exists_index]
  rintro hfg _ f rfl - rfl g rfl - hgf
  exact hfg <| by simpa [sum_add_distrib, hi] using congr_arg (∑ j ∈ s, · j) hgf.symm

