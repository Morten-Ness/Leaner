import Mathlib

variable (K : Type u) [Field K]

variable (V W : FGModuleCat K)

theorem FGModuleCatCoevaluation_apply_one :
    (FGModuleCat.FGModuleCatCoevaluation K V).hom (1 : K) =
      ∑ i : Module.Basis.ofVectorSpaceIndex K V,
        (Module.Basis.ofVectorSpace K V) i ⊗ₜ[K] (Module.Basis.ofVectorSpace K V).coord i := coevaluation_apply_one K V

