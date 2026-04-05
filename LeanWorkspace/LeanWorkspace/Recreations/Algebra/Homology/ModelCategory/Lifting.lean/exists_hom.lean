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

set_option backward.isDefEq.respectTransparency false in
include hQ hK in
theorem exists_hom (n m : ℤ) (hnm : n + 1 = m := by lia) :
    ∃ (φ : Q.X n ⟶ K.X m), π.f n ≫ φ ≫ ι.f m = (CochainComplex.Lifting.cocycle₁' sq hsq).1.v n m hnm := by
  have : Epi π := Cofork.IsColimit.epi hQ
  obtain ⟨l, hl⟩ := CokernelCofork.IsColimit.desc'
    ((CokernelCofork.isColimitMapCoconeEquiv _ _).1
    (isColimitOfPreserves (HomologicalComplex.eval _ _ n) hQ))
    ((CochainComplex.Lifting.cocycle₁' sq hsq).1.v n m hnm) (by simp)
  dsimp [CokernelCofork.map] at l hl
  obtain ⟨l', hl'⟩ := KernelFork.IsLimit.lift' ((KernelFork.isLimitMapConeEquiv _ _).1
    (isLimitOfPreserves (HomologicalComplex.eval _ _ m) hK)) l (by
      simp [← cancel_epi (π.f n), reassoc_of% hl])
  exact ⟨l', by cat_disch⟩

