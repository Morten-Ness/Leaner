import Mathlib

variable (C : Type u) [Category.{v} C] [Abelian C]

set_option backward.isDefEq.respectTransparency false in
theorem hasExt_iff [HasDerivedCategory.{w'} C] :
    HasExt.{w} C ↔ ∀ (X Y : C) (n : ℤ) (_ : 0 ≤ n), Small.{w}
      ((singleFunctor C 0).obj X ⟶
        (((singleFunctor C 0).obj Y)⟦n⟧)) := by
  dsimp [HasExt]
  simp only [hasSmallLocalizedShiftedHom_iff _ _ Q]
  constructor
  · intro h X Y n hn
    exact (small_congr ((shiftFunctorZero _ ℤ).app
      ((singleFunctor C 0).obj X)).homFromEquiv).1 (h X Y 0 n)
  · intro h X Y a b
    obtain hab | hab := le_or_gt a b
    · refine (small_congr ?_).1 (h X Y (b - a) (by simpa))
      exact (Functor.FullyFaithful.ofFullyFaithful
        (shiftFunctor _ a)).homEquiv.trans
        ((shiftFunctorAdd' _ _ _ _ (Int.sub_add_cancel b a)).symm.app _).homToEquiv
    · suffices Subsingleton ((Q.obj ((CochainComplex.singleFunctor C 0).obj X))⟦a⟧ ⟶
          (Q.obj ((CochainComplex.singleFunctor C 0).obj Y))⟦b⟧) from inferInstance
      constructor
      intro x y
      rw [← cancel_mono ((Q.commShiftIso b).inv.app _),
        ← cancel_epi ((Q.commShiftIso a).hom.app _)]
      have : (((CochainComplex.singleFunctor C 0).obj X)⟦a⟧).IsStrictlyLE (-a) :=
        CochainComplex.isStrictlyLE_shift _ 0 _ _ (by lia)
      have : (((CochainComplex.singleFunctor C 0).obj Y)⟦b⟧).IsStrictlyGE (-b) :=
        CochainComplex.isStrictlyGE_shift _ 0 _ _ (by lia)
      apply (subsingleton_hom_of_isStrictlyLE_of_isStrictlyGE _ _ (-a) (-b) (by
        lia)).elim

