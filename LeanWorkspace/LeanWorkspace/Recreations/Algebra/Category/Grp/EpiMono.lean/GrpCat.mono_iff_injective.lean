import Mathlib

open scoped Pointwise

variable {A B : GrpCat.{u}} (f : A ⟶ B)

theorem mono_iff_injective : Mono f ↔ Function.Injective f := Iff.trans (GrpCat.mono_iff_ker_eq_bot f) <| MonoidHom.ker_eq_bot_iff f.hom

