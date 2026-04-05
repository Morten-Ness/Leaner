import Mathlib

variable {α : Type*} {R : Type*} {M : Type*}

variable [Semiring R] [AddCommGroup M] [Module R M]

theorem neg_iSup {ι : Sort*} (S : ι → Submodule R M) : (-⨆ i, S i) = ⨆ i, -S i := (Submodule.negOrderIso : Submodule R M ≃o Submodule R M).map_iSup _

