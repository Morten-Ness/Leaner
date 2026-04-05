import Mathlib

open scoped Pointwise

variable {A B : GrpCat.{u}} (f : A ⟶ B)

theorem surjective_of_epi [Epi f] : Function.Surjective f := by
  dsimp [Function.Surjective]
  by_contra! ⟨b, hb⟩
  exact
    SurjectiveOfEpiAuxs.g_ne_h f b (fun ⟨c, hc⟩ => hb _ hc)
      (congr_arg GrpCat.Hom.hom ((cancel_epi f).1 (SurjectiveOfEpiAuxs.comp_eq f)))

