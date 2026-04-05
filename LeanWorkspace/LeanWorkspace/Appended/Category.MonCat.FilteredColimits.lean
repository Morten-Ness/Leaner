import Mathlib

section

variable {J : Type v} [SmallCategory J] (F : J ⥤ MonCat.{max v u})

theorem M.map_mk {j k : J} (f : j ⟶ k) (x : F.obj j) :
    M.mk F ⟨k, F.map f x⟩ = M.mk F ⟨j, x⟩ := MonCat.FilteredColimits.M.mk_eq _ _ _ ⟨k, 𝟙 _, f, by simp⟩

end

section

variable {J : Type v} [SmallCategory J] (F : J ⥤ MonCat.{max v u})

theorem M.mk_eq (x y : Σ j, F.obj j)
    (h : ∃ (k : J) (f : x.1 ⟶ k) (g : y.1 ⟶ k), F.map f x.2 = F.map g y.2) :
    M.mk.{v, u} F x = M.mk F y := Quot.eqvGen_sound (Types.FilteredColimit.eqvGen_colimitTypeRel_of_rel (F ⋙ forget MonCat) x y h)

end

section

variable {J : Type v} [SmallCategory J] (F : J ⥤ MonCat.{max v u})

theorem M.mk_surjective (m : M.{v, u} F) :
    ∃ (j : J) (x : F.obj j), M.mk F ⟨j, x⟩ = m := (F ⋙ forget MonCat).ιColimitType_jointly_surjective m

end

section

variable {J : Type v} [SmallCategory J] (F : J ⥤ MonCat.{max v u})

variable [IsFiltered J]

theorem cocone_naturality {j j' : J} (f : j ⟶ j') :
    F.map f ≫ MonCat.FilteredColimits.coconeMorphism.{v, u} F j' = MonCat.FilteredColimits.coconeMorphism F j := MonCat.ext fun x =>
    congr_fun ((Types.TypeMax.colimitCocone (F ⋙ forget MonCat)).ι.naturality f) x

end

section

variable {J : Type v} [SmallCategory J] (F : J ⥤ MonCat.{max v u})

variable [IsFiltered J]

theorem colimitMulAux_eq_of_rel_left {x x' y : Σ j, F.obj j}
    (hxx' : Types.FilteredColimit.Rel (F ⋙ forget MonCat) x x') :
    MonCat.FilteredColimits.colimitMulAux.{v, u} F x y = MonCat.FilteredColimits.colimitMulAux.{v, u} F x' y := by
  obtain ⟨j₁, x⟩ := x; obtain ⟨j₂, y⟩ := y; obtain ⟨j₃, x'⟩ := x'
  obtain ⟨l, f, g, hfg⟩ := hxx'
  replace hfg : F.map f x = F.map g x' := by simpa
  obtain ⟨s, α, β, γ, h₁, h₂, h₃⟩ :=
    IsFiltered.tulip (IsFiltered.leftToMax j₁ j₂) (IsFiltered.rightToMax j₁ j₂)
      (IsFiltered.rightToMax j₃ j₂) (IsFiltered.leftToMax j₃ j₂) f g
  apply MonCat.FilteredColimits.M.mk_eq
  use s, α, γ
  simp_rw [map_mul, ← ConcreteCategory.comp_apply, ← F.map_comp, h₁, h₂, h₃, F.map_comp,
    ConcreteCategory.comp_apply, hfg]

end

section

variable {J : Type v} [SmallCategory J] (F : J ⥤ MonCat.{max v u})

variable [IsFiltered J]

theorem colimitMulAux_eq_of_rel_right {x y y' : Σ j, F.obj j}
    (hyy' : Types.FilteredColimit.Rel (F ⋙ forget MonCat) y y') :
    MonCat.FilteredColimits.colimitMulAux.{v, u} F x y = MonCat.FilteredColimits.colimitMulAux.{v, u} F x y' := by
  obtain ⟨j₁, y⟩ := y; obtain ⟨j₂, x⟩ := x; obtain ⟨j₃, y'⟩ := y'
  obtain ⟨l, f, g, hfg⟩ := hyy'
  simp only [Functor.comp_obj, Functor.comp_map, forget_map] at hfg
  obtain ⟨s, α, β, γ, h₁, h₂, h₃⟩ :=
    IsFiltered.tulip (IsFiltered.rightToMax j₂ j₁) (IsFiltered.leftToMax j₂ j₁)
      (IsFiltered.leftToMax j₂ j₃) (IsFiltered.rightToMax j₂ j₃) f g
  apply MonCat.FilteredColimits.M.mk_eq
  use s, α, γ
  dsimp
  simp_rw [map_mul, ← ConcreteCategory.comp_apply, ← F.map_comp, h₁, h₂, h₃, F.map_comp,
    ConcreteCategory.comp_apply, hfg]

end

section

variable {J : Type v} [SmallCategory J] (F : J ⥤ MonCat.{max v u})

variable [IsFiltered J]

theorem colimit_mul_mk_eq' {j : J} (x y : F.obj j) :
    M.mk.{v, u} F ⟨j, x⟩ * M.mk.{v, u} F ⟨j, y⟩ = M.mk.{v, u} F ⟨j, x * y⟩ := by
  simpa using MonCat.FilteredColimits.colimit_mul_mk_eq F ⟨j, x⟩ ⟨j, y⟩ j (𝟙 _) (𝟙 _)

end

section

variable {J : Type v} [SmallCategory J] (F : J ⥤ MonCat.{max v u})

variable [IsFiltered J]

theorem colimit_mul_mk_eq (x y : Σ j, F.obj j) (k : J) (f : x.1 ⟶ k) (g : y.1 ⟶ k) :
    M.mk.{v, u} F x * M.mk F y = M.mk F ⟨k, F.map f x.2 * F.map g y.2⟩ := by
  obtain ⟨j₁, x⟩ := x; obtain ⟨j₂, y⟩ := y
  obtain ⟨s, α, β, h₁, h₂⟩ := IsFiltered.bowtie (IsFiltered.leftToMax j₁ j₂) f
    (IsFiltered.rightToMax j₁ j₂) g
  refine MonCat.FilteredColimits.M.mk_eq F _ _ ?_
  use s, α, β
  dsimp
  simp_rw [map_mul, ← ConcreteCategory.comp_apply, ← F.map_comp, h₁, h₂]

end

section

variable {J : Type v} [SmallCategory J] (F : J ⥤ MonCat.{max v u})

variable [IsFiltered J]

theorem colimit_one_eq (j : J) : (1 : M.{v, u} F) = M.mk F ⟨j, 1⟩ := by
  apply MonCat.FilteredColimits.M.mk_eq
  refine ⟨max' _ j, IsFiltered.leftToMax _ j, IsFiltered.rightToMax _ j, ?_⟩
  simp

end
