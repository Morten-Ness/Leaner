import Mathlib

variable {K : Type*}

variable [DivisionRing K]

theorem cast_mk' (a b h1 h2) : ((⟨a, b, h1, h2⟩ : ℚ) : K) = a / b := Rat.cast_def _

