import Mathlib

variable {R : Type u} [Ring R] {X Y : ModuleCat.{v} R} (f : X ⟶ Y)

variable {M : Type v} [AddCommGroup M] [Module R M]

theorem mono_iff_ker_eq_bot : Mono f ↔ LinearMap.ker f.hom = ⊥ := ⟨fun _ => ModuleCat.ker_eq_bot_of_mono _, fun hf =>
    ConcreteCategory.mono_of_injective _ <| by convert LinearMap.ker_eq_bot.1 hf⟩

