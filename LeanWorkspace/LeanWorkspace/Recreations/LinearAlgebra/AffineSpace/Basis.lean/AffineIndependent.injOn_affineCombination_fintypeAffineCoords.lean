import Mathlib

variable {ι k V P : Type*} [Ring k] [AddCommGroup V] [Module k V] [AddTorsor V P]

variable (ι k) in

theorem AffineIndependent.injOn_affineCombination_fintypeAffineCoords [Fintype ι] {p : ι → P}
    (h : AffineIndependent k p) :
    InjOn (Finset.univ.affineCombination k p) (fintypeAffineCoords ι k) := fun w₁ hw₁ w₂ hw₂ he ↦ (affineIndependent_iff_eq_of_fintype_affineCombination_eq k p).1
    h w₁ w₂ (mem_fintypeAffineCoords_iff_sum.1 hw₁) (mem_fintypeAffineCoords_iff_sum.1 hw₂) he

