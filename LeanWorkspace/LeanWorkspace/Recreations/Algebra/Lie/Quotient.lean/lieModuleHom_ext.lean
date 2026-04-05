import Mathlib

variable {R : Type u} {L : Type v} {M : Type w}

variable [CommRing R] [LieRing L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M]

variable (N N' : LieSubmodule R L M)

variable [LieAlgebra R L] [LieModule R L M] (I J : LieIdeal R L)

theorem lieModuleHom_ext ⦃f g : M ⧸ N →ₗ⁅R,L⁆ M⦄ (h : f.comp (LieSubmodule.Quotient.mk' N) = g.comp (LieSubmodule.Quotient.mk' N)) : f = g := LieModuleHom.ext fun x => LieSubmodule.Quotient.inductionOn' x <| LieModuleHom.congr_fun h

