import Mathlib

variable (S : ShortComplex Ab.{u})

theorem ab_exact_iff_ker_le_range : S.Exact ↔ S.g.hom.ker ≤ S.f.hom.range := S.ab_exact_iff

