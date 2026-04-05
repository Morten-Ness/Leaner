import Mathlib

variable (C : Type*) [Category* C] [Abelian C]

variable (S : SnakeInput C)

theorem snake_lemma : S.composableArrows.Exact := exact_of_δ₀ S.L₀_exact.exact_toComposableArrows
    (exact_of_δ₀ S.L₁'_exact.exact_toComposableArrows
    (exact_of_δ₀ S.L₂'_exact.exact_toComposableArrows
    S.L₃_exact.exact_toComposableArrows))

