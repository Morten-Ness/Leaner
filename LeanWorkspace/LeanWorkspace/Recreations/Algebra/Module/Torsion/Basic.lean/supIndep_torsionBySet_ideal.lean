import Mathlib

variable {R M : Type*}

variable [CommSemiring R] [AddCommMonoid M] [Module R M] (s : Set R) (a : R)

variable {ι : Type*} {p : ι → Ideal R} {S : Finset ι}

theorem supIndep_torsionBySet_ideal (hp : (S : Set ι).Pairwise fun i j => p i ⊔ p j = ⊤) :
    S.SupIndep fun i => Submodule.torsionBySet R M <| p i := fun T hT i hi hiT => by
  rw [disjoint_iff, Finset.sup_eq_iSup,
    Submodule.iSup_torsionBySet_ideal_eq_torsionBySet_iInf fun i hi j hj ij => hp (hT hi) (hT hj) ij]
  have := GaloisConnection.u_inf
    (b₁ := OrderDual.toDual (p i)) (b₂ := OrderDual.toDual (⨅ i ∈ T, p i)) (Submodule.torsion_gc R M)
  dsimp at this ⊢
  rw [← this, Ideal.sup_iInf_eq_top, top_coe, Submodule.torsionBySet_univ]
  intro j hj; apply hp hi (hT hj); rintro rfl; exact hiT hj

