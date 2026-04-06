import Mathlib

variable {G H : Type*} [Mul G] [Mul H] {A B : Finset G} {a0 b0 : G}

theorem mulHom_preimage (f : G →ₙ* H) (hf : Function.Injective f) (a0 b0 : G) {A B : Finset H}
    (u : UniqueMul A B (f a0) (f b0)) :
    UniqueMul (A.preimage f hf.injOn) (B.preimage f hf.injOn) a0 b0 := by
  intro a b ha hb hab
  have ha' : f a ∈ A := by
    simpa [Finset.mem_preimage] using ha
  have hb' : f b ∈ B := by
    simpa [Finset.mem_preimage] using hb
  have hmul : f a * f b = f a0 * f b0 := by
    simpa [map_mul] using congrArg f hab
  rcases u ha' hb' hmul with ⟨hfa, hfb⟩
  exact ⟨hf hfa, hf hfb⟩
