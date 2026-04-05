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

theorem comp_coe_cocyle₁'_v_eq_zero (n m : ℤ) (hnm : n + 1 = m := by lia) :
    i.f n ≫ (CochainComplex.Lifting.cocycle₁' sq hsq).1.v n m hnm = 0 := by
  have fac_left (k : ℤ) := (hsq k).fac_left
  dsimp at fac_left
  simp [CochainComplex.Lifting.cocycle₁', fac_left, reassoc_of% fac_left]

