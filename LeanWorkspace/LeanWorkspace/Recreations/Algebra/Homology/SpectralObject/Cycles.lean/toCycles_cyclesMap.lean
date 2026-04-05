import Mathlib

variable {C ι : Type*} [Category* C] [Category* ι] [Abelian C]

variable (X : SpectralObject C ι)

variable {i j k : ι} (f : i ⟶ j) (g : j ⟶ k)
  {i' j' k' : ι} (f' : i' ⟶ j') (g' : j' ⟶ k')
  {i'' j'' k'' : ι} (f'' : i'' ⟶ j'') (g'' : j'' ⟶ k'')

variable (fg : i ⟶ k) (h : f ≫ g = fg) (fg' : i' ⟶ k') (h' : f' ≫ g' = fg')

theorem toCycles_cyclesMap (α : mk₂ f g ⟶ mk₂ f' g') (β : mk₁ fg ⟶ mk₁ fg') (n : ℤ)
    (hβ₀ : β.app 0 = α.app 0 := by cat_disch) (hβ₁ : β.app 1 = α.app 2 := by cat_disch) :
    X.toCycles f g fg h n ≫ X.cyclesMap f g f' g' α n =
      (X.H n).map β ≫ X.toCycles f' g' fg' h' n := by
  rw [← cancel_mono (X.iCycles f' g' n), Category.assoc, Category.assoc, CategoryTheory.Abelian.SpectralObject.toCycles_i,
    X.cyclesMap_i f g f' g' α (homMk₁ (α.app 1) (α.app 2) (naturality' α 1 2)) n rfl,
    toCycles_i_assoc, ← Functor.map_comp, ← Functor.map_comp]
  congr 1
  ext
  · dsimp
    rw [hβ₀]
    exact naturality' α 0 1
  · dsimp
    rw [hβ₁, Category.comp_id, Category.id_comp]

