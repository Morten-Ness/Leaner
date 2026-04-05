FAIL
import Mathlib

variable {k P₁ P₂ P₃ P₄ V₁ V₂ V₃ V₄ : Type*} [Ring k]
  [AddCommGroup V₁] [AddCommGroup V₂] [AddCommGroup V₃] [AddCommGroup V₄]
  [Module k V₁] [Module k V₂] [Module k V₃] [Module k V₄]
  [AddTorsor V₁ P₁] [AddTorsor V₂ P₂] [AddTorsor V₃ P₃] [AddTorsor V₄ P₄]

theorem toEquiv_inj {e e' : P₁ ≃ᵃ[k] P₂} : e.toEquiv = e'.toEquiv ↔ e = e' := by
  constructor
  · intro h
    cases e with
    | mk e le he =>
      cases e' with
      | mk e' le' he' =>
        dsimp at h
        subst h
        have hle : le = le' := by
          ext v
          let p : P₁ := Classical.choice (AddTorsor.nonempty P₁)
          have hp := he p v
          have hp' := he' p v
          dsimp at hp hp'
          rw [← hp, ← hp']
        subst hle
        have hhe : he = he' := by
          apply Subsingleton.elim
        subst hhe
        rfl
  · intro h
    subst h
    rfl
