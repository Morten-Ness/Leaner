import Mathlib

variable {ι : Sort*} {α M : Type*}

variable [One M]

theorem mulSupport_iInf [ConditionallyCompleteLattice M] [Nonempty ι] (f : ι → α → M) :
    mulSupport (fun x ↦ ⨅ i, f i x) ⊆ ⋃ i, mulSupport (f i) := Function.mulSupport_iSup (M := Mᵒᵈ) f

