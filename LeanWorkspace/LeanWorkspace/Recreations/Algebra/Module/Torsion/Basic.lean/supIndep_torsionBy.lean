import Mathlib

open scoped Function -- required for scoped `on` notation

variable {R M : Type*}

variable [CommSemiring R] [AddCommMonoid M] [Module R M] (s : Set R) (a : R)

variable {ι : Type*} {p : ι → Ideal R} {S : Finset ι}

variable {q : ι → R}

theorem supIndep_torsionBy (hq : (S : Set ι).Pairwise <| (IsCoprime on q)) :
    S.SupIndep fun i => Submodule.torsionBy R M <| q i := by
  convert Submodule.supIndep_torsionBySet_ideal (M := M) fun i hi j hj ij =>
      (Ideal.sup_eq_top_iff_isCoprime (q i) _).mpr <| hq hi hj ij
  exact (Submodule.torsionBySet_span_singleton_eq (R := R) (M := M) _).symm

