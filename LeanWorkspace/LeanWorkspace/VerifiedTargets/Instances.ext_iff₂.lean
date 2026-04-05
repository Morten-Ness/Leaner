import Mathlib

variable {M : Type uM} {N : Type uN} {P : Type uP} {Q : Type uQ}

theorem ext_iff₂ {_ : MulOneClass M} {_ : MulOneClass N} {_ : CommMonoid P} {f g : M →* N →* P} :
    f = g ↔ ∀ x y, f x y = g x y := DFunLike.ext_iff.trans <| forall_congr' fun _ => DFunLike.ext_iff

