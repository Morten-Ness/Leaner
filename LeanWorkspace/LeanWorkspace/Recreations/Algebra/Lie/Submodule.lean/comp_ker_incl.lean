import Mathlib

variable {R : Type u} {L : Type v} {M : Type w} {N : Type w₁}

variable [CommRing R] [LieRing L]

variable [AddCommGroup M] [Module R M] [LieRingModule L M]

variable [AddCommGroup N] [Module R N] [LieRingModule L N]

variable (f : M →ₗ⁅R,L⁆ N)

theorem comp_ker_incl : f.comp f.ker.incl = 0 := by ext ⟨m, hm⟩; exact LieModuleHom.mem_ker.mp hm

