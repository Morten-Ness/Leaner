import Mathlib

variable {ι : Type*}

variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V]

variable (X₀ X₁ X₂ : V) (d₀ : X₁ ⟶ X₀) (d₁ : X₂ ⟶ X₁) (s : d₁ ≫ d₀ = 0)
  (succ : ∀ (S : ShortComplex V), Σ' (X₃ : V) (d₂ : X₃ ⟶ S.X₁), d₂ ≫ S.f = 0)

variable (succ' : ∀ {X₀ X₁ : V} (f : X₁ ⟶ X₀), Σ' (X₂ : V) (d : X₂ ⟶ X₁), d ≫ f = 0)

theorem mk'_d (n : ℕ) :
    (ChainComplex.mk' X₀ X₁ d₀ succ').d (n + 2) (n + 1) = (ChainComplex.mk'XIso X₀ X₁ d₀ succ' n).hom ≫
      (succ' ((ChainComplex.mk' X₀ X₁ d₀ succ').d (n + 1) n)).2.1 := by
  obtain _ | n := n
  · dsimp [ChainComplex.mk'XIso, ChainComplex.mk']
    rw [ChainComplex.mk_d_2_1]
    apply ChainComplex.mk'_congr_succ'_d
    rw [ChainComplex.mk_d_1_0]
  · apply ChainComplex.mk_d

