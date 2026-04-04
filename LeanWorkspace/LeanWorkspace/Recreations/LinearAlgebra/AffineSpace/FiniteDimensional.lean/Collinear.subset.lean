import Mathlib

variable (k : Type*) {V : Type*} {P : Type*}

variable {ι : Type*}

variable [DivisionRing k] [AddCommGroup V] [Module k V] [AddTorsor V P]

variable {k}

variable (k)

theorem Collinear.subset {s₁ s₂ : Set P} (hs : s₁ ⊆ s₂) (h : Collinear k s₂) : Collinear k s₁ := (Submodule.rank_mono (vectorSpan_mono k hs)).trans h

