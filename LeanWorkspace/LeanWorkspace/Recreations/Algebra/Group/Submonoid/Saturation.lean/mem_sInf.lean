import Mathlib

variable {M : Type*} [MulOneClass M]

theorem mem_sInf {f : Set (SaturatedSubmonoid M)} {x : M} : x ∈ Submonoid.MulSaturated.sInf f ↔ ∀ s ∈ f, x ∈ s := Set.mem_iInter₂

