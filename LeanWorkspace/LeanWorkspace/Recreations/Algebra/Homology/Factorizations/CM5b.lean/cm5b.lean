import Mathlib

variable {C : Type*} [Category* C] [Abelian C] [EnoughInjectives C]
  {K L : CochainComplex C ℤ} (f : K ⟶ L)

theorem cm5b (n : ℤ) [K.IsStrictlyGE (n + 1)] [L.IsStrictlyGE n] :
    ∃ (L' : CochainComplex C ℤ) (_hL' : L'.IsStrictlyGE n)
      (CochainComplex.cm5b.i : K ⟶ L') (p : L' ⟶ L) (_hi : Mono CochainComplex.cm5b.i)
      (_hp : degreewiseEpiWithInjectiveKernel p) (_hp' : QuasiIso p),
      CochainComplex.cm5b.i ≫ p = f := ⟨_ , by infer_instance, cm5b.i f, cm5b.p K L, inferInstance,
    CochainComplex.cm5b.degreewiseEpiWithInjectiveKernel_p cm5b K L, inferInstance, by simp⟩

