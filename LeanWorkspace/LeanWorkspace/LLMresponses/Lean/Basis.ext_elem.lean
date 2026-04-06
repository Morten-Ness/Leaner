FAIL
import Mathlib

variable {ι ι' G G' k V P : Type*} [AddCommGroup V] [AddTorsor V P]

variable [Ring k] [Module k V] (b : AffineBasis ι k P) {s : Finset ι} {i j : ι} (e : ι ≃ ι')

theorem ext_elem [Finite ι] {q₁ q₂ : P} (h : ∀ i, b.coord i q₁ = b.coord i q₂) : q₁ = q₂ := by
  let f : P → ι → k := fun q i => b.coord i q
  have hf_inj : Function.Injective f := by
    intro q₁ q₂ hq
    exact b.independent.injective <| by
      ext i
      exact hq i
  exact hf_inj (funext h)
