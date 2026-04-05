import Mathlib

variable {C : Type*} [Category* C] [Abelian C]

variable {A B X Y : CochainComplex C ℤ}
  {t : A ⟶ X} {i : A ⟶ B} {p : X ⟶ Y} {b : B ⟶ Y}
  (sq : CommSq t i p b)
  (hsq : ∀ n, (sq.map (HomologicalComplex.eval _ _ n)).LiftStruct)
  {Q : CochainComplex C ℤ} {π : B ⟶ Q} {hπ : i ≫ π = 0}
  (hQ : IsColimit (CokernelCofork.ofπ _ hπ))
  {K : CochainComplex C ℤ} {ι : K ⟶ X} {hι : ι ≫ p = 0}
  (hK : IsLimit (KernelFork.ofι _ hι))

theorem comp_coe_cocycle₁_comp :
    (Cochain.ofHom π).comp ((CochainComplex.Lifting.cocycle₁ sq hsq hQ hK).1.comp (.ofHom ι)
        (add_zero 1)) (zero_add 1) =
      (CochainComplex.Lifting.cocycle₁' sq hsq).1 := by
  ext n m hnm
  simp [CochainComplex.Lifting.cocycle₁]

