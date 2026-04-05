import Mathlib

open scoped Function in -- required for scoped `on` notation

variable {R M : Type*}

variable [CommRing R] [AddCommGroup M] [Module R M]

variable {ι : Type*} [DecidableEq ι] {S : Finset ι}

theorem torsionBy_isInternal {q : ι → R} (hq : (S : Set ι).Pairwise <| (IsCoprime on q))
    (hM : Module.IsTorsionBy R M <| ∏ i ∈ S, q i) :
    DirectSum.IsInternal fun i : S => Submodule.torsionBy R M <| q i := by
  rw [← Module.isTorsionBySet_span_singleton_iff, Ideal.submodule_span_eq, ←
    Ideal.finset_inf_span_singleton _ _ hq, Finset.inf_eq_iInf] at hM
  convert Submodule.torsionBySet_isInternal
      (fun i hi j hj ij => (Ideal.sup_eq_top_iff_isCoprime (q i) _).mpr <| hq hi hj ij) hM
  exact (Submodule.torsionBySet_span_singleton_eq _ (R := R) (M := M)).symm

