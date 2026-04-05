import Mathlib

section

open scoped DirectSum

variable {ι R : Type*} {G : ι → Type*} [DecidableEq ι] [∀ i, AddCommGroup (G i)] [CommMonoid R]

theorem directSum_injective :
    Function.Injective (AddChar.directSum : (∀ i, AddChar (G i) R) → AddChar (⨁ i, G i) R) := by
  refine toAddMonoidHomEquiv.symm.injective.comp <| DirectSum.toAddMonoid_injective.comp ?_
  rintro ψ χ h
  simpa [funext_iff] using h

end
