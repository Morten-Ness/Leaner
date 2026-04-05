import Mathlib

variable {K : Type u} [Field K]

theorem symm {A B : CSA K} (h : IsBrauerEquivalent A B) : IsBrauerEquivalent B A := let ⟨n, m, hn, hm, ⟨iso⟩⟩ := h
  ⟨m, n, hm, hn, ⟨iso.symm⟩⟩

