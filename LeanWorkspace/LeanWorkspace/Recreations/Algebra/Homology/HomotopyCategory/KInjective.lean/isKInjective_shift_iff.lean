import Mathlib

variable {C : Type*} [Category* C] [Abelian C]

theorem isKInjective_shift_iff (L : CochainComplex C ℤ) (n : ℤ) :
    (L⟦n⟧).IsKInjective ↔ L.IsKInjective := ⟨fun _ ↦ CochainComplex.isKInjective_of_iso (show L⟦n⟧⟦-n⟧ ≅ L from (shiftEquiv _ n).unitIso.symm.app L),
    fun _ ↦ inferInstance⟩

