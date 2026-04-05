import Mathlib

theorem DivInvMonoid.ext {M : Type*} ⦃m₁ m₂ : DivInvMonoid M⦄
    (h_mul : (letI := m₁; HMul.hMul : M → M → M) = (letI := m₂; HMul.hMul : M → M → M))
    (h_inv : (letI := m₁; Inv.inv : M → M) = (letI := m₂; Inv.inv : M → M)) : m₁ = m₂ := by
  have h_mon := Monoid.ext h_mul
  have h₁ : m₁.one = m₂.one := congr_arg (·.one) h_mon
  let f : @MonoidHom M M m₁.toMulOne m₂.toMulOne :=
    @MonoidHom.mk _ _ (_) _ (@OneHom.mk _ _ (_) _ id h₁)
      (fun x y => congr_fun (congr_fun h_mul x) y)
  have : m₁.zpow = m₂.zpow := by
    ext m x
    exact @MonoidHom.map_zpow' M M m₁ m₂ f (congr_fun h_inv) x m
  have : m₁.div = m₂.div := by
    ext a b
    exact (@div_eq_mul_inv _ m₁ a b).trans
      (((congr_fun (congr_fun h_mul a) _).trans
        (congr_arg _ (congr_fun h_inv b))).trans (@div_eq_mul_inv _ m₂ a b).symm)
  rcases m₁ with @⟨_, ⟨_⟩, ⟨_⟩⟩
  congr

