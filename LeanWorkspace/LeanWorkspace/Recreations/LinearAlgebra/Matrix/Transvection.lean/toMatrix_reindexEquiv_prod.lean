import Mathlib

variable (n p : Type*) (R : Type u₂) {𝕜 : Type*} [Field 𝕜]

variable [DecidableEq n] [DecidableEq p]

variable [CommRing R]

variable {R n} (i j : n)

variable [Fintype n] [Fintype p]

theorem toMatrix_reindexEquiv_prod (e : n ≃ p) (L : List (Matrix.TransvectionStruct n R)) :
    (L.map (Matrix.TransvectionStruct.toMatrix ∘ Matrix.TransvectionStruct.reindexEquiv e)).prod = reindexAlgEquiv R _ e (L.map Matrix.TransvectionStruct.toMatrix).prod := by
  induction L with
  | nil => simp
  | cons t L IH =>
    simp only [Matrix.TransvectionStruct.toMatrix_reindexEquiv, IH, Function.comp_apply, List.prod_cons,
      reindexAlgEquiv_apply, List.map]
    exact (reindexAlgEquiv_mul R _ _ _ _).symm

