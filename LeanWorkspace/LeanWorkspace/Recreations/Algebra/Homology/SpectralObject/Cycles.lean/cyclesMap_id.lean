import Mathlib

variable {C ι : Type*} [Category* C] [Category* ι] [Abelian C]

variable (X : SpectralObject C ι)

variable {i j k : ι} (f : i ⟶ j) (g : j ⟶ k)
  {i' j' k' : ι} (f' : i' ⟶ j') (g' : j' ⟶ k')
  {i'' j'' k'' : ι} (f'' : i'' ⟶ j'') (g'' : j'' ⟶ k'')

theorem cyclesMap_id (n : ℤ) :
    X.cyclesMap f g f g (𝟙 _) n = 𝟙 _ := by
  rw [← cancel_mono (X.iCycles f g n), X.cyclesMap_i f g f g (𝟙 _) (𝟙 _) n,
    Functor.map_id, Category.comp_id, Category.id_comp]

