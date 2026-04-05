import Mathlib

variable {α M : Type*} [One M]

theorem HasFiniteMulSupport.iInf [ConditionallyCompleteLattice M] {ι : Sort*} [Nonempty ι]
    [Finite ι] {f : ι → α → M} (hf : ∀ i, HasFiniteMulSupport (f i)) :
    HasFiniteMulSupport fun a ↦ ⨅ i, f i a := (Set.finite_iUnion hf).subset <| mulSupport_iInf f

