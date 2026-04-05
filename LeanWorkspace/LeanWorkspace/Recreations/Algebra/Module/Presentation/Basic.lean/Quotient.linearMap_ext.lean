import Mathlib

variable (A : Type u) [Ring A]

variable {A} (relations : Relations.{w₀, w₁} A)

theorem Quotient.linearMap_ext {M : Type v} [AddCommGroup M] [Module A M]
    {f f' : relations.Quotient →ₗ[A] M}
    (h : ∀ (g : relations.G), f (relations.toQuotient (Finsupp.single g 1)) =
      f' (relations.toQuotient (Finsupp.single g 1))) :
    f = f' := Submodule.linearMap_qext _ (Finsupp.lhom_ext' (fun g ↦ LinearMap.ext_ring (h g)))

