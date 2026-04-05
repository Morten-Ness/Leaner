import Mathlib

variable {C ι : Type*} [Category* C] [Category* ι] [Abelian C]

variable (X : SpectralObject C ι)

variable {i j k : ι} (f : i ⟶ j) (g : j ⟶ k)
  {i' j' k' : ι} (f' : i' ⟶ j') (g' : j' ⟶ k')
  {i'' j'' k'' : ι} (f'' : i'' ⟶ j'') (g'' : j'' ⟶ k'')

variable (fg : i ⟶ k) (h : f ≫ g = fg) (fg' : i' ⟶ k') (h' : f' ≫ g' = fg')

theorem opcyclesMap_fromOpcycles (α : mk₂ f g ⟶ mk₂ f' g') (β : mk₁ fg ⟶ mk₁ fg') (n : ℤ)
    (hβ₀ : β.app 0 = α.app 0 := by cat_disch) (hβ₁ : β.app 1 = α.app 2 := by cat_disch) :
    X.opcyclesMap f g f' g' α n ≫ X.fromOpcycles f' g' fg' h' n =
      X.fromOpcycles f g fg h n ≫ (X.H n).map β := by
  rw [← cancel_epi (X.pOpcycles f g n), p_fromOpcycles_assoc,
    X.p_opcyclesMap_assoc f g f' g' α (homMk₁ (α.app 0) (α.app 1)
      (naturality' α 0 1)) n rfl,
    CategoryTheory.Abelian.SpectralObject.p_fromOpcycles, ← Functor.map_comp, ← Functor.map_comp]
  congr 1
  ext
  · cat_disch
  · dsimp
    rw [hβ₁]
    exact (naturality' α 1 2).symm

