import Mathlib

variable {ι : Type*}

variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V]

variable (X₀ X₁ X₂ : V) (d₀ : X₁ ⟶ X₀) (d₁ : X₂ ⟶ X₁) (s : d₁ ≫ d₀ = 0)
  (succ : ∀ (S : ShortComplex V), Σ' (X₃ : V) (d₂ : X₃ ⟶ S.X₁), d₂ ≫ S.f = 0)

set_option backward.isDefEq.respectTransparency false in
theorem mk_d (n : ℕ) :
    (ChainComplex.mk X₀ X₁ X₂ d₀ d₁ s succ).d (n + 3) (n + 2) =
      (ChainComplex.mkXIso X₀ X₁ X₂ d₀ d₁ s succ n).hom ≫ (succ
        (ShortComplex.mk _ _ (HomologicalComplex.d_comp_d (ChainComplex.mk X₀ X₁ X₂ d₀ d₁ s succ) (n + 2) (n + 1) n))).2.1 := by
  have eq := ChainComplex.mk_congr_succ_d₂ succ
    (ChainComplex.mkAux_eq_shortComplex_mk_d_comp_d X₀ X₁ X₂ d₀ d₁ s succ n)
  rw [eqToHom_refl, comp_id] at eq
  refine Eq.trans ?_ eq
  dsimp only [ChainComplex.mk, ChainComplex.of]
  rw [dif_pos (by rfl), eqToHom_refl, id_comp]
  rfl

