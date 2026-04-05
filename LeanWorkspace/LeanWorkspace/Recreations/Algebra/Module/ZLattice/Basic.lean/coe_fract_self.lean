import Mathlib

variable {E ι : Type*}

variable {K : Type*} [NormedField K]

variable [NormedAddCommGroup E] [NormedSpace K E]

variable (b : Basis ι K E)

variable [LinearOrder K]

variable [IsStrictOrderedRing K]

variable [FloorRing K]

variable [Fintype ι]

variable [Unique ι]

theorem coe_fract_self (k : K) : (ZSpan.fract (Module.Basis.singleton ι K) k : K) = Int.fract k := Module.Basis.ext_elem (Module.Basis.singleton ι K) fun _ => by
    rw [ZSpan.repr_fract_apply, Module.Basis.singleton_repr, Module.Basis.singleton_repr]

