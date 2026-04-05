import Mathlib

variable {R : Type u} [Semiring R]

variable {ι : Type v} [dec_ι : DecidableEq ι]

variable {M : Type*} [AddCommMonoid M] [Module R M]

variable (A : ι → Submodule R M)

theorem coeLinearMap_of (i : ι) (x : A i) : DirectSum.coeLinearMap A (of (fun i ↦ A i) i x) = x := -- Porting note: spelled out arguments. (I don't know how this works.)
  toAddMonoid_of (β := fun i => A i) (fun i ↦ ((A i).subtype : A i →+ M)) i x

