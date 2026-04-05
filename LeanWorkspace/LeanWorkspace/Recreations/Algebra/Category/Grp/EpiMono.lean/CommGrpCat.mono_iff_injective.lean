import Mathlib

open scoped Pointwise

variable {A B : CommGrpCat.{u}} (f : A ⟶ B)

theorem mono_iff_injective : Mono f ↔ Function.Injective f := Iff.trans (CommGrpCat.mono_iff_ker_eq_bot f) <| MonoidHom.ker_eq_bot_iff f.hom

