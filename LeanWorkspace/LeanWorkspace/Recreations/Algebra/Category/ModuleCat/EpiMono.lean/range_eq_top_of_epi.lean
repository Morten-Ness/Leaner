import Mathlib

variable {R : Type u} [Ring R] {X Y : ModuleCat.{v} R} (f : X ⟶ Y)

variable {M : Type v} [AddCommGroup M] [Module R M]

theorem range_eq_top_of_epi [Epi f] : LinearMap.range f.hom = ⊤ := LinearMap.range_eq_top_of_cancel fun u v h => ModuleCat.hom_ext_iff.mp <|
    (@cancel_epi _ _ _ _ _ f _ (↟u) (↟v)).1 <| ModuleCat.hom_ext_iff.mpr h

