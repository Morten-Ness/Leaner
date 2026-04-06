FAIL
import Mathlib

variable {α M : Type*} [One M]

variable {β : Type*} {f : β → M} {g : α → β}

theorem HasFiniteMulSupport.of_comp [One β] (hfg : (f ∘ g).HasFiniteMulSupport) (h : f 1 = 1)
    (hf : Function.Injective f) :
    g.HasFiniteMulSupport := by
  classical
  rw [Function.HasFiniteMulSupport] at hfg ⊢
  refine Set.Finite.subset hfg ?_
  intro a ha
  rw [Function.mem_mulSupport] at ha ⊢
  exact mt (fun hg => hf <| by simpa [Function.comp, hg] using h) ha
