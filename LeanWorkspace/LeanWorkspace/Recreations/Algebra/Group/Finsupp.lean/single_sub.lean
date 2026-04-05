import Mathlib

variable {ι F M N O G H : Type*}

variable [AddGroup G] {p : ι → Prop} {v v' : ι →₀ G}

theorem single_sub (a : ι) (b₁ b₂ : G) : single a (b₁ - b₂) = single a b₁ - single a b₂ := (Finsupp.singleAddHom a : G →+ _).map_sub b₁ b₂

