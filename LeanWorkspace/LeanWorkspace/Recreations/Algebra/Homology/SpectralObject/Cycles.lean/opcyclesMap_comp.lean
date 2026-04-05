import Mathlib

variable {C ι : Type*} [Category* C] [Category* ι] [Abelian C]

variable (X : SpectralObject C ι)

variable {i j k : ι} (f : i ⟶ j) (g : j ⟶ k)
  {i' j' k' : ι} (f' : i' ⟶ j') (g' : j' ⟶ k')
  {i'' j'' k'' : ι} (f'' : i'' ⟶ j'') (g'' : j'' ⟶ k'')

theorem opcyclesMap_comp (α : mk₂ f g ⟶ mk₂ f' g') (α' : mk₂ f' g' ⟶ mk₂ f'' g'')
    (α'' : mk₂ f g ⟶ mk₂ f'' g'') (n : ℤ) (h : α ≫ α' = α'' := by cat_disch) :
    X.opcyclesMap f g f' g' α n ≫ X.opcyclesMap f' g' f'' g'' α' n =
      X.opcyclesMap f g f'' g'' α'' n := by
  subst h
  rw [← cancel_epi (X.pOpcycles f g n),
    X.p_opcyclesMap_assoc f g f' g' α _ ,
    X.p_opcyclesMap f' g' f'' g'' α' _ ,
    ← Functor.map_comp_assoc]
  exact (X.p_opcyclesMap _ _ _ _ _ _ _ (by cat_disch)).symm

