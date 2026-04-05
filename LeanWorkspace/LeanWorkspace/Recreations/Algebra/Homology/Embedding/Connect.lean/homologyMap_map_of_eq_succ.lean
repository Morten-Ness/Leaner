import Mathlib

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

variable {K K' K'' : ChainComplex C ℕ} {L L' L'' : CochainComplex C ℕ}

variable (h : ConnectData K L) (h' : ConnectData K' L') (h'' : ConnectData K'' L'')

set_option backward.isDefEq.respectTransparency false in
theorem homologyMap_map_of_eq_succ (n : ℕ) [NeZero n] (m : ℤ) (hmn : m = n)
    [HasHomology h.cochainComplex m] [HasHomology L n]
    [HasHomology h'.cochainComplex m] [HasHomology L' n] :
    homologyMap (h.map h' fK fL f_comm) m =
    (h.homologyIsoPos n m hmn).hom ≫ homologyMap fL n ≫ (h'.homologyIsoPos n m hmn).inv := by
  rw [← cancel_mono (HomologicalComplex.homologyι ..)]
  dsimp [CochainComplex.ConnectData.homologyIsoPos]
  simp only [homologyι_naturality, Category.assoc, restrictionHomologyIso_hom_homologyι,
    homologyι_naturality_assoc, restrictionHomologyIso_inv_homologyι_assoc]
  congr 1
  rw [← cancel_epi (HomologicalComplex.pOpcycles ..)]
  subst hmn
  simp

