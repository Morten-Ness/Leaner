import Mathlib

variable {ι ι₁ ι₂ : Type*} {c : ComplexShape ι} {c₁ : ComplexShape ι₁} {c₂ : ComplexShape ι₂}

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (e₁ : Embedding c₁ c) (e₂ : Embedding c₂ c)

variable (ac : AreComplementary e₁ e₂)

variable {X : ι → Type*} (x₁ : ∀ i₁, X (e₁.f i₁)) (x₂ : ∀ i₂, X (e₂.f i₂))

omit ac in
theorem desc.aux_trans {i j k : ι} (hij : i = j) (hjk : j = k) (x : X i) :
    ComplexShape.Embedding.AreComplementary.desc.aux X j k hjk (aux X i j hij x) = ComplexShape.Embedding.AreComplementary.desc.aux X i k (hij.trans hjk) x := by
  subst hij hjk
  rfl

