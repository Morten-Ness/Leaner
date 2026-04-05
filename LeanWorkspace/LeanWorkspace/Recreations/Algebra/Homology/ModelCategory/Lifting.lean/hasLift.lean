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

theorem hasLift (α : Cochain Q K 0) (hα : δ 0 1 α = (CochainComplex.Lifting.cocycle₁ sq hsq hQ hK).1) :
    sq.HasLift where
  exists_lift := by
    replace hα : (Cochain.ofHom π).comp ((δ 0 1 α).comp (.ofHom ι) (add_zero 1)) (zero_add 1) =
        (CochainComplex.Lifting.cocycle₁' sq hsq).1 := by
      rw [← CochainComplex.Lifting.comp_coe_cocycle₁_comp sq hsq hQ hK, hα]
    let l : Cocycle B X 0 :=
      Cocycle.mk (cochain₀ sq hsq -
        (Cochain.ofHom π).comp
          (α.comp (.ofHom ι) (add_zero 0)) (zero_add 0)) 1 (by simp) (by
            ext p _ rfl
            replace hα := Cochain.congr_v hα p _ rfl
            simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Cochain.comp_zero_cochain_v,
              δ_zero_cochain_v, Preadditive.sub_comp, Category.assoc, Preadditive.comp_sub,
              HomologicalComplex.Hom.comm_assoc, CochainComplex.Lifting.cocycle₁', Cocycle.mk_coe, Cochain.ofHoms_v,
              HomologicalComplex.eval_obj, HomologicalComplex.eval_map] at hα
            simp [hα])
    exact ⟨{
      l := l.homOf
      fac_left := by
        ext n
        have h₁ : i.f n ≫ π.f n = 0 := by
          simp [← HomologicalComplex.comp_f, hπ]
        have h₂ := (hsq n).fac_left
        dsimp at h₁ h₂
        simp [l, reassoc_of% h₁, h₂]
      fac_right := by
        ext n
        have : ι.f n ≫ p.f n = 0 := by
          simp [← HomologicalComplex.comp_f, hι]
        simpa [l, this] using (hsq n).fac_right }⟩

