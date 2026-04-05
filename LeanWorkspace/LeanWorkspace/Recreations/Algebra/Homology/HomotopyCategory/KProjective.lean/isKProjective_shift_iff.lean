import Mathlib

variable {C : Type*} [Category* C] [Abelian C]

theorem isKProjective_shift_iff (K : CochainComplex C ℤ) (n : ℤ) :
    (K⟦n⟧).IsKProjective ↔ K.IsKProjective := ⟨fun _ ↦ CochainComplex.isKProjective_of_iso (show K⟦n⟧⟦-n⟧ ≅ K from (shiftEquiv _ n).unitIso.symm.app K),
    fun _ ↦ inferInstance⟩

