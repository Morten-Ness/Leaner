import Mathlib

variable {R M : Type*}

variable [CommRing R] [AddCommGroup M] [Module R M]

variable {ι : Type*} [DecidableEq ι] {S : Finset ι}

theorem torsionBySet_isInternal {p : ι → Ideal R}
    (hp : (S : Set ι).Pairwise fun i j => p i ⊔ p j = ⊤)
    (hM : Module.IsTorsionBySet R M (⨅ i ∈ S, p i : Ideal R)) :
    DirectSum.IsInternal fun i : S => Submodule.torsionBySet R M <| p i := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (iSupIndep_comp_coe_iff_supIndep.mpr <| Submodule.supIndep_torsionBySet_ideal hp)
    (by
      apply (iSup_subtype'' ↑S fun i => Submodule.torsionBySet R M <| p i).trans
      -- Porting note: times out if we change apply below to <|
      apply (Submodule.iSup_torsionBySet_ideal_eq_torsionBySet_iInf hp).trans <|
        (Module.isTorsionBySet_iff_torsionBySet_eq_top _).mp hM)

