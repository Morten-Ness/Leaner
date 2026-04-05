import Mathlib

variable {ι μ μ' : Type*}

variable [DecidableEq ι] [AddCommMonoid μ] [HasAntidiagonal μ] [DecidableEq μ] {n : μ}

variable {s : Finset ι} {n : μ} {f : ι → μ}

theorem finsetCongr_piAntidiag_eq_antidiag (n : μ) :
    Equiv.finsetCongr (Equiv.boolArrowEquivProd _) (Finset.piAntidiag univ n) = antidiagonal n := by
  ext ⟨x₁, x₂⟩
  simp_rw [Equiv.finsetCongr_apply, mem_map, Equiv.toEmbedding, Function.Embedding.coeFn_mk,
    ← Equiv.eq_symm_apply]
  simp [add_comm]

