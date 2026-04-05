import Mathlib

open scoped Function -- required for scoped `on` notation

variable {R M : Type*}

variable [CommSemiring R] [AddCommMonoid M] [Module R M] (s : Set R) (a : R)

variable {ι : Type*} {p : ι → Ideal R} {S : Finset ι}

variable {q : ι → R}

theorem iSup_torsionBy_eq_torsionBy_prod (hq : (S : Set ι).Pairwise <| (IsCoprime on q)) :
    ⨆ i ∈ S, Submodule.torsionBy R M (q i) = Submodule.torsionBy R M (∏ i ∈ S, q i) := by
  rw [← Submodule.torsionBySet_span_singleton_eq, Ideal.submodule_span_eq, ←
    Ideal.finset_inf_span_singleton _ _ hq, Finset.inf_eq_iInf, ←
    Submodule.iSup_torsionBySet_ideal_eq_torsionBySet_iInf]
  · congr
    ext : 1
    congr
    ext : 1
    exact (Submodule.torsionBySet_span_singleton_eq _).symm
  exact fun i hi j hj ij => (Ideal.sup_eq_top_iff_isCoprime _ _).mpr (hq hi hj ij)

