import Mathlib

variable (C : Type*) [Category* C] [Abelian C]

variable (S : SnakeInput C)

set_option backward.isDefEq.respectTransparency false in
theorem op_δ : S.op.δ = S.δ.op := Quiver.Hom.unop_inj (by
  rw [Quiver.Hom.unop_op, ← cancel_mono (pushout.inr _ _ : _ ⟶ S.P'),
    ← cancel_epi (pullback.snd _ _ : S.P ⟶ _), S.snd_δ_inr,
    ← cancel_mono S.P'IsoUnopOpP.hom, ← cancel_epi S.PIsoUnopOpP'.inv,
    CategoryTheory.ShortComplex.SnakeInput.P'IsoUnopOpP, CategoryTheory.ShortComplex.SnakeInput.PIsoUnopOpP', assoc, assoc, assoc, assoc,
    pushoutIsoUnopPullback_inr_hom, pullbackIsoUnopPushout_inv_snd_assoc,
    pushoutIsoUnopPullback_inl_hom, pullbackIsoUnopPushout_inv_fst_assoc]
  apply Quiver.Hom.op_inj
  simpa only [op_comp, Quiver.Hom.op_unop, assoc] using S.CategoryTheory.ShortComplex.SnakeInput.snd_δ_inr CategoryTheory.ShortComplex.SnakeInput.op)

