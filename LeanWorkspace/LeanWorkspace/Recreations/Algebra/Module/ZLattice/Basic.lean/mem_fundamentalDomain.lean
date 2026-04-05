import Mathlib

variable {E ι : Type*}

variable {K : Type*} [NormedField K]

variable [NormedAddCommGroup E] [NormedSpace K E]

variable (b : Basis ι K E)

variable [LinearOrder K]

theorem mem_fundamentalDomain {m : E} :
    m ∈ ZSpan.fundamentalDomain b ↔ ∀ i, b.repr m i ∈ Set.Ico (0 : K) 1 := Iff.rfl

