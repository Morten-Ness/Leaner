import Mathlib

variable {M : Type*} {S T : Set M}

variable [Mul M]

theorem subset_centralizer_centralizer : S ⊆ S.centralizer.centralizer := fun x hx _ hy ↦ (hy x hx).symm

