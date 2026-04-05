import Mathlib

section

variable {R : Type u} [Ring R] {X Y : ModuleCat.{v} R} (f : X ⟶ Y)

variable {M : Type v} [AddCommGroup M] [Module R M]

theorem epi_iff_range_eq_top : Epi f ↔ LinearMap.range f.hom = ⊤ := ⟨fun _ => ModuleCat.range_eq_top_of_epi _, fun hf =>
    ConcreteCategory.epi_of_surjective _ <| by convert LinearMap.range_eq_top.1 hf⟩

end

section

variable {R : Type u} [Ring R] {X Y : ModuleCat.{v} R} (f : X ⟶ Y)

variable {M : Type v} [AddCommGroup M] [Module R M]

theorem epi_iff_surjective : Epi f ↔ Function.Surjective f := by
  rw [ModuleCat.epi_iff_range_eq_top, LinearMap.range_eq_top]

end

section

variable {R : Type u} [Ring R] {X Y : ModuleCat.{v} R} (f : X ⟶ Y)

variable {M : Type v} [AddCommGroup M] [Module R M]

theorem ker_eq_bot_of_mono [Mono f] : LinearMap.ker f.hom = ⊥ := LinearMap.ker_eq_bot_of_cancel fun u v h => ModuleCat.hom_ext_iff.mp <|
    (@cancel_mono _ _ _ _ _ f _ (↟u) (↟v)).1 <| ModuleCat.hom_ext_iff.mpr h

end

section

variable {R : Type u} [Ring R] {X Y : ModuleCat.{v} R} (f : X ⟶ Y)

variable {M : Type v} [AddCommGroup M] [Module R M]

theorem mono_iff_injective : Mono f ↔ Function.Injective f := by
  rw [ModuleCat.mono_iff_ker_eq_bot, LinearMap.ker_eq_bot]

end

section

variable {R : Type u} [Ring R] {X Y : ModuleCat.{v} R} (f : X ⟶ Y)

variable {M : Type v} [AddCommGroup M] [Module R M]

theorem mono_iff_ker_eq_bot : Mono f ↔ LinearMap.ker f.hom = ⊥ := ⟨fun _ => ModuleCat.ker_eq_bot_of_mono _, fun hf =>
    ConcreteCategory.mono_of_injective _ <| by convert LinearMap.ker_eq_bot.1 hf⟩

end

section

variable {R : Type u} [Ring R] {X Y : ModuleCat.{v} R} (f : X ⟶ Y)

variable {M : Type v} [AddCommGroup M] [Module R M]

theorem range_eq_top_of_epi [Epi f] : LinearMap.range f.hom = ⊤ := LinearMap.range_eq_top_of_cancel fun u v h => ModuleCat.hom_ext_iff.mp <|
    (@cancel_epi _ _ _ _ _ f _ (↟u) (↟v)).1 <| ModuleCat.hom_ext_iff.mpr h

end
