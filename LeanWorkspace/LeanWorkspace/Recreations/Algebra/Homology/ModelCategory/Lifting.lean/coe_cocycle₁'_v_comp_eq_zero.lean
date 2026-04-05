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

theorem coe_cocycle₁'_v_comp_eq_zero (n m : ℤ) (hnm : n + 1 = m := by lia) :
    (CochainComplex.Lifting.cocycle₁' sq hsq).1.v n m hnm ≫ p.f m = 0 := by
  have fac_right (k : ℤ) := (hsq k).fac_right
  dsimp at fac_right
  simp [CochainComplex.Lifting.cocycle₁', -HomologicalComplex.Hom.comm,
    ← p.comm, fac_right, reassoc_of% fac_right, b.comm]

