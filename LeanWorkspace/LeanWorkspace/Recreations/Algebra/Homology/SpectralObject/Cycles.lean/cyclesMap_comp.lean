import Mathlib

variable {C ι : Type*} [Category* C] [Category* ι] [Abelian C]

variable (X : SpectralObject C ι)

variable {i j k : ι} (f : i ⟶ j) (g : j ⟶ k)
  {i' j' k' : ι} (f' : i' ⟶ j') (g' : j' ⟶ k')
  {i'' j'' k'' : ι} (f'' : i'' ⟶ j'') (g'' : j'' ⟶ k'')

theorem cyclesMap_comp (α : mk₂ f g ⟶ mk₂ f' g') (α' : mk₂ f' g' ⟶ mk₂ f'' g'')
    (α'' : mk₂ f g ⟶ mk₂ f'' g'') (n : ℤ) (h : α ≫ α' = α'' := by cat_disch) :
    X.cyclesMap f g f' g' α n ≫ X.cyclesMap f' g' f'' g'' α' n =
      X.cyclesMap f g f'' g'' α'' n := by
  subst h
  rw [← cancel_mono (X.iCycles f'' g'' n), Category.assoc,
    X.cyclesMap_i f' g' f'' g'' α' _ n rfl,
    X.cyclesMap_i_assoc f g f' g' α _ n rfl,
    ← Functor.map_comp]
  exact (X.cyclesMap_i _ _ _ _ _ _ _).symm

