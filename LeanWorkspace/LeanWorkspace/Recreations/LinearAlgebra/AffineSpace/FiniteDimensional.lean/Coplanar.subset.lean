import Mathlib

variable (k : Type*) {V : Type*} {P : Type*}

variable {ι : Type*}

variable [DivisionRing k] [AddCommGroup V] [Module k V] [AddTorsor V P]

variable {k}

variable (k)

variable (k P)

variable {P}

variable (k) in

theorem Coplanar.subset {s₁ s₂ : Set P} (hs : s₁ ⊆ s₂) (h : Coplanar k s₂) : Coplanar k s₁ := (Submodule.rank_mono (vectorSpan_mono k hs)).trans h

