import Mathlib

variable {M : Type*} [Monoid M] [HasDistribNeg M] {a b : M}

theorem neg_left (h : Associated a b) : Associated (-a) b := let ⟨u, hu⟩ := h; ⟨-u, by simp [hu]⟩

