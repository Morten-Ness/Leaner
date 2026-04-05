import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (S : ShortComplex C) {S₁ S₂ S₃ : ShortComplex C}

set_option backward.isDefEq.respectTransparency false in
theorem hasKernel [S.HasRightHomology] [HasCokernel S.f] :
    HasKernel (cokernel.desc S.f S.g S.zero) := by
  let h := S.rightHomologyData
  haveI : HasLimit (parallelPair h.g' 0) := ⟨⟨⟨_, h.hι'⟩⟩⟩
  let e : parallelPair (cokernel.desc S.f S.g S.zero) 0 ≅ parallelPair h.g' 0 :=
    parallelPair.ext (IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) h.hp)
      (Iso.refl _) (coequalizer.hom_ext (by simp)) (by simp)
  exact hasLimit_of_iso e.symm

