import Mathlib

variable {R : Type u} [Ring R]

variable (S : ShortComplex (ModuleCat.{v} R))

theorem moduleCat_pOpcycles_eq_iff (x y : S.X₂) :
    S.pOpcycles x = S.pOpcycles y ↔ x - y ∈ LinearMap.range S.f.hom := Iff.trans ⟨fun h => by simpa using congr(S.moduleCatOpcyclesIso.hom $h),
    fun h => (ModuleCat.mono_iff_injective S.moduleCatOpcyclesIso.hom).1 inferInstance (by simpa)⟩
    (Submodule.Quotient.eq _)

