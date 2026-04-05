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

theorem π_f_cochain₁_v_ι_f (n m : ℤ) (hnm : n + 1 = m) :
    π.f n ≫ (CochainComplex.Lifting.cochain₁ sq hsq hQ hK).v n m hnm ≫ ι.f m = (CochainComplex.Lifting.cocycle₁' sq hsq).1.v n m hnm := (CochainComplex.Lifting.exists_hom sq hsq hQ hK n m hnm).choose_spec

