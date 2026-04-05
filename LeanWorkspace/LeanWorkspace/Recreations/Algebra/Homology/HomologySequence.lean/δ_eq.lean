import Mathlib

variable {C ι : Type*} [Category* C] [Abelian C] {c : ComplexShape ι}
  {S : ShortComplex (HomologicalComplex C c)}
  (hS : S.ShortExact) (i j : ι) (hij : c.Rel i j)

theorem δ_eq {A : C} (x₃ : A ⟶ S.X₃.X i) (hx₃ : x₃ ≫ S.X₃.d i j = 0)
    (x₂ : A ⟶ S.X₂.X i) (hx₂ : x₂ ≫ S.g.f i = x₃)
    (x₁ : A ⟶ S.X₁.X j) (hx₁ : x₁ ≫ S.f.f j = x₂ ≫ S.X₂.d i j)
    (k : ι) (hk : c.next j = k) :
    S.X₃.liftCycles x₃ j (c.next_eq' hij) hx₃ ≫ S.X₃.homologyπ i ≫ hS.δ i j hij =
      S.X₁.liftCycles x₁ k hk (by
        have := hS.mono_f
        rw [← cancel_mono (S.f.f k), assoc, ← S.f.comm, reassoc_of% hx₁,
          d_comp_d, comp_zero, zero_comp]) ≫ S.X₁.homologyπ j := by
  simpa only [assoc] using CategoryTheory.ShortComplex.ShortExact.δ_eq' hS i j hij (S.X₃.liftCycles x₃ j
    (c.next_eq' hij) hx₃ ≫ S.X₃.homologyπ i)
    (x₂ ≫ S.X₂.pOpcycles i) (S.X₁.liftCycles x₁ k hk _)
      (by simp only [assoc, HomologicalComplex.p_opcyclesMap,
        HomologicalComplex.homology_π_ι,
        HomologicalComplex.liftCycles_i_assoc, reassoc_of% hx₂])
      (by rw [← cancel_mono (S.X₂.iCycles j), HomologicalComplex.liftCycles_comp_cyclesMap,
        HomologicalComplex.liftCycles_i, assoc, assoc, HomologicalComplex.opcyclesToCycles_iCycles,
        HomologicalComplex.p_fromOpcycles, hx₁])

