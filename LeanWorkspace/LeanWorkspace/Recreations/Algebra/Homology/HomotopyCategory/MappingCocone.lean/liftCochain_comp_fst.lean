import Mathlib

variable {C : Type*} [Category* C] [Preadditive C]
  {K L : CochainComplex C ℤ} (φ : K ⟶ L)

variable [HasHomotopyCofiber φ]

variable {M : CochainComplex C ℤ} {n m : ℤ}
  (α : Cochain M K n) (β : Cochain M L m) (h : m + 1 = n)

theorem liftCochain_comp_fst :
    (CochainComplex.mappingCocone.liftCochain φ α β h).comp (Cochain.ofHom (CochainComplex.mappingCocone.fst φ)) (add_zero _) = α := by
  cat_disch

