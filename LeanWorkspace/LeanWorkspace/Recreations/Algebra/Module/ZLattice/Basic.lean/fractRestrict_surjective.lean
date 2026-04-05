import Mathlib

variable {E ι : Type*}

variable {K : Type*} [NormedField K]

variable [NormedAddCommGroup E] [NormedSpace K E]

variable (b : Basis ι K E)

variable [LinearOrder K]

variable [IsStrictOrderedRing K]

variable [FloorRing K]

variable [Fintype ι]

theorem fractRestrict_surjective : Function.Surjective (ZSpan.fractRestrict b) := fun x => ⟨↑x, Subtype.ext (ZSpan.fract_eq_self.mpr (Subtype.mem x))⟩

