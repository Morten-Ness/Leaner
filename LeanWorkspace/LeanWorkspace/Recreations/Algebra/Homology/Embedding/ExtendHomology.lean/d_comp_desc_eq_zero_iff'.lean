import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C] [HasZeroMorphisms C]
  [HasZeroObject C]

variable (K L M : HomologicalComplex C c) (φ : K ⟶ L) (φ' : L ⟶ M) (e : c.Embedding c')

variable {i j k : ι} {i' j' k' : ι'} (hj' : e.f j = j')
  (hi : c.prev j = i) (hi' : c'.prev j' = i') (hk : c.next j = k) (hk' : c'.next j' = k')

variable (cocone : CokernelCofork (K.d i j)) (hcocone : IsColimit cocone)

variable (cone : KernelFork (hcocone.desc (CokernelCofork.ofπ (K.d j k) (K.d_comp_d i j k))))
  (hcone : IsLimit cone)

include hk hk' hcocone in
theorem d_comp_desc_eq_zero_iff' ⦃W : C⦄ (f' : cocone.pt ⟶ K.X k)
    (hf' : cocone.π ≫ f' = K.d j k)
    (f'' : cocone.pt ⟶ (K.extend e).X k')
    (hf'' : (extendXIso K e hj').hom ≫ cocone.π ≫ f'' = (K.extend e).d j' k')
    (φ : W ⟶ cocone.pt) :
    φ ≫ f' = 0 ↔ φ ≫ f'' = 0 := by
  by_cases hjk : c.Rel j k
  · have hk'' : e.f k = k' := by rw [← hk', ← hj', c'.next_eq' (e.rel hjk)]
    have : f' ≫ (K.extendXIso e hk'').inv = f'' := by
      apply Cofork.IsColimit.hom_ext hcocone
      rw [reassoc_of% hf', ← cancel_epi (extendXIso K e hj').hom, hf'',
        K.extend_d_eq e hj' hk'']
    rw [← cancel_mono (K.extendXIso e hk'').inv, zero_comp, assoc, this]
  · have h₁ : f' = 0 := by
      apply Cofork.IsColimit.hom_ext hcocone
      simp only [hf', comp_zero, K.shape _ _ hjk]
    have h₂ : f'' = 0 := by
      apply Cofork.IsColimit.hom_ext hcocone
      rw [← cancel_epi (extendXIso K e hj').hom, hf'', comp_zero, comp_zero,
        K.extend_d_from_eq_zero e j' k' j hj']
      rw [hk]
      exact hjk
    simp [h₁, h₂]

