import Mathlib

variable {E ι : Type*}

variable {K : Type*} [NormedField K]

variable [NormedAddCommGroup E] [NormedSpace K E]

variable (b : Basis ι K E)

variable [LinearOrder K]

variable [IsStrictOrderedRing K]

variable [FloorRing K]

theorem exist_unique_vadd_mem_fundamentalDomain [Finite ι] (x : E) :
    ∃! v : span ℤ (Set.range b), v +ᵥ x ∈ ZSpan.fundamentalDomain b := by
  cases nonempty_fintype ι
  refine ⟨-ZSpan.floor b x, ?_, fun y h => ?_⟩
  · exact (ZSpan.vadd_mem_fundamentalDomain b (-ZSpan.floor b x) x).mpr rfl
  · exact (ZSpan.vadd_mem_fundamentalDomain b y x).mp h

