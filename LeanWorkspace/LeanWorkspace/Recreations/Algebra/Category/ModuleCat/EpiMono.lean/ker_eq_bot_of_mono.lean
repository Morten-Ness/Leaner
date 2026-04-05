import Mathlib

variable {R : Type u} [Ring R] {X Y : ModuleCat.{v} R} (f : X ⟶ Y)

variable {M : Type v} [AddCommGroup M] [Module R M]

theorem ker_eq_bot_of_mono [Mono f] : LinearMap.ker f.hom = ⊥ := LinearMap.ker_eq_bot_of_cancel fun u v h => ModuleCat.hom_ext_iff.mp <|
    (@cancel_mono _ _ _ _ _ f _ (↟u) (↟v)).1 <| ModuleCat.hom_ext_iff.mpr h

