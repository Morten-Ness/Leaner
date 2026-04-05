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

theorem coe_floor_self (k : K) : (ZSpan.floor (Module.Basis.singleton ι K) k : K) = ⌊k⌋ := Module.Basis.ext_elem (Module.Basis.singleton ι K) fun _ => by
    rw [ZSpan.repr_floor_apply, Module.Basis.singleton_repr, Module.Basis.singleton_repr]

