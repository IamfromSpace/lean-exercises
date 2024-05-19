def foil_sub_add (a b c d : Nat) : (a - b) * (c + d) = a * c + a * d - b * c - b * d :=
  calc (a - b) * (c + d)
    _ = a * (c + d) - b * (c + d) := by rw [Nat.mul_sub_right_distrib a b (c + d)]
    _ = a * c + a * d - b * (c + d) := by rw [Nat.left_distrib a c d]
    _ = a * c + a * d - (b * c + b * d) := by rw [Nat.left_distrib b c d]
    _ = a * c + a * d - b * c - b * d := by rw [Nat.sub_add_eq _ _]

def foil_add (a b c d : Nat) : (a + b) * (c + d) = a * c + a * d + b * c + b * d :=
  calc (a + b) * (c + d)
    _ = a * (c + d) + b * (c + d) := by rw [Nat.right_distrib a b (c + d)]
    _ = a * c + a * d + b * (c + d) := by rw [Nat.left_distrib a c d]
    _ = a * c + a * d + (b * c + b * d) := by rw [Nat.left_distrib b c d]
    _ = a * c + a * d + b * c + b * d := by rw [Eq.symm (Nat.add_assoc _ _ _)]


def power_push (x y : Nat) : x * x^y = x^(y + 1) :=
   Eq.symm (Eq.trans (Nat.pow_succ x y) (Nat.mul_comm (x^y) x))

def x_ge_1_to_any_power_ge_1 {x : Nat} (y : Nat) (h : 1 ≤ x) : 1 ≤ x^y :=
  let h₁ : 1^y ≤ x^y := Nat.pow_le_pow_of_le_left h y
  let h₂ : 1^y = 1 :=
    Nat.rec
      (motive := λ z ↦ 1^z = 1)
      (Eq.refl _)
      (λ z (h₃ : 1^z = 1) ↦
        let h₄ : 1 * 1^z = 1 * 1 := congrArg (λ xx ↦ 1 * xx) h₃
        let h₅ : 1^(z + 1) = 1 * 1 := Eq.trans (Eq.symm (power_push 1 z)) h₄
        let h₆ : 1^(z + 1) = 1 := by simp [h₅]
        h₆
      )
      y

  Eq.subst
    (motive := λ sub ↦ sub ≤ x^y)
    h₂
    h₁

def xxy_ge_xy (x y : Nat) : x * y ≤ x * (x * y) :=
  Nat.rec
    (motive := λ z ↦ z * y ≤ z * (z * y))
    (Nat.le_of_eq (by simp [Eq.refl _]))
    (λ z (h₁ : z * y ≤ z * (z * y)) ↦
      let zero_le_2zy₁ : 0 + (z + z) * y = (z + z) * y := by simp [Eq.refl _]
      let zero_le_2zy : 0 ≤ (z + z) * y := Nat.le.intro zero_le_2zy₁

      let h₂ : y + z * y ≤ y + z * (z * y) := Nat.add_le_add_left h₁ y
      let h₃ : 1 * y + z * y ≤ 1 * y + z * (z * y) := by simp [h₂]
      let h₄ : (1 + z) * y ≤ 1 * y + z * (z * y) :=
        Eq.subst
          (motive := λ sub ↦ sub ≤ 1 * y + z * (z * y))
          (Eq.symm (Nat.right_distrib 1 z y))
          h₃
      let h₅ : (z + 1) * y ≤ 1 * y + z * (z * y) :=
        Eq.subst
          (motive := λ sub ↦ sub * y ≤ 1 * y + z * (z * y))
          (Nat.add_comm 1 z)
          h₄
      let h₆ : (z + 1) * y ≤ 1 * y + (z * z) * y :=
        Eq.subst
          (motive := λ sub ↦ (z + 1) * y ≤ 1 * y + sub)
          (Eq.symm (Nat.mul_assoc z z y))
          h₅
      let h₇ : (z + 1) * y ≤ (1 + (z * z)) * y :=
        Eq.subst
          (motive := λ sub ↦ (z + 1) * y ≤ sub)
          (Eq.symm (Nat.right_distrib 1 (z * z) y))
          h₆
      let h₈ : (z + 1) * y + 0 ≤ (1 + (z * z)) * y + (z + z) * y := Nat.add_le_add h₇ zero_le_2zy
      let h₉ : (z + 1) * y + 0 ≤ ((1 + (z * z)) + (z + z)) * y :=
        Eq.subst
          (motive := λ sub ↦ (z + 1) * y + 0 ≤ sub)
          (Eq.symm (Nat.right_distrib (1 + (z * z)) (z + z) y))
          h₈
      let h₁₀ : (z + 1) * y + 0 ≤ ((z * z) + 1 + (z + z)) * y :=
        Eq.subst
          (motive := λ sub ↦ (z + 1) * y + 0 ≤ (sub + (z + z)) * y)
          (Nat.add_comm 1 (z * z))
          h₉
      let h₁₁ : (z + 1) * y + 0 ≤ ((z * z) + (1 + (z + z))) * y :=
        Eq.subst
          (motive := λ sub ↦ (z + 1) * y + 0 ≤ sub * y)
          (Nat.add_assoc (z * z) 1 (z + z))
          h₁₀
      let h₁₂ : (z + 1) * y + 0 ≤ ((z * z) + (z + z + 1)) * y :=
        Eq.subst
          (motive := λ sub ↦ (z + 1) * y + 0 ≤ ((z * z) + sub) * y)
          (Nat.add_comm 1 (z + z))
          h₁₁
      let h₁₃ : (z + 1) * y + 0 ≤ ((z * z) + (z + z) + 1) * y :=
        Eq.subst
          (motive := λ sub ↦ (z + 1) * y + 0 ≤ sub * y)
          (Eq.symm (Nat.add_assoc (z * z) (z + z) 1))
          h₁₂
      let h₁₄ : (z + 1) * y + 0 ≤ ((z * z) + z + z + 1) * y :=
        Eq.subst
          (motive := λ sub ↦ (z + 1) * y + 0 ≤ (sub + 1) * y)
          (Eq.symm (Nat.add_assoc (z * z) z z))
          h₁₃
      let h₁₅ : (z + 1) * y + 0 ≤ ((z * z) + (z * 1) + (1 * z) + (1 * 1)) * y :=
        Eq.subst
          (motive := λ sub ↦ (z + 1) * y + 0 ≤ sub * y)
          (by simp)
          h₁₄
      let h₁₆ : (z + 1) * y + 0 ≤ (z + 1) * (z + 1) * y :=
        Eq.subst
          (motive := λ sub ↦ (z + 1) * y + 0 ≤ sub * y)
          (Eq.symm (foil_add z 1 z 1))
          h₁₅

      Eq.subst
        (motive := λ sub ↦ (z + 1) * y ≤ sub)
        (Nat.mul_assoc (z + 1) (z + 1) y)
        h₁₆
    )
    x


theorem mikes_challenge : ∀ (b : Nat), ∀ (n : Nat), b > 0 → (∃ (x : Nat), (b - 1) * x = b^n - 1) :=
    λ b n (h : 1 ≤ b) ↦
      Nat.rec
        (motive := λ m ↦ ∃ (x : Nat), (b - 1) * x = b^m - 1)
        (Exists.intro 0 (Eq.refl _))
        (λ m ⟨x, h₁⟩ ↦
          let h₂ : b * x - 1 * x = b^m - 1 := Eq.trans (Eq.symm (Nat.mul_sub_right_distrib b 1 x)) h₁
          let h₃ : b^m - 1 = b * x - x := by simp [Eq.symm h₂]
          let h₄ : b^m - 1 + 1 = b * x - x + 1 := by simp [h₃]
          let h₅ : b^m = b * x - x + 1 := Eq.trans (Eq.symm (Nat.sub_add_cancel (x_ge_1_to_any_power_ge_1 m h))) h₄
          let h₆ : b * b^m = b * (b * x - x + 1) := by simp [h₅]
          let h₇ : b * b^m = b * (b * x - x) + b := by simp [Eq.trans h₆ (Nat.left_distrib b (b * x - x) 1)]
          let h₈ : b * b^m = b * (b * x) - b * x + b := by rw [h₇, Nat.mul_sub_left_distrib b (b * x) x]
          let h₉ : b^(m + 1) = b * (b * x) - b * x + b := Eq.trans (Eq.symm (power_push b m)) h₈
          let h₁₀ : b^(m + 1) - 1 = b * (b * x) - b * x + b - 1 := by simp [h₉]
          let h₁₁ : b^(m + 1) - 1 = (b + (b * (b * x) - b * x)) - 1 := by rw [h₁₀, Nat.add_comm _ b]
          let h₁₂ : b^(m + 1) - 1 = b + b * (b * x) - b * x - 1 := by rw [h₁₁, Eq.symm (Nat.add_sub_assoc (xxy_ge_xy b x) b)]
          let h₁₃ : b^(m + 1) - 1 = b * (b * x) + b - b * x - 1 := by rw [h₁₂, (Nat.add_comm b _)]
          let h₁₄ : b^(m + 1) - 1 = b * (b * x) + (b * 1) - 1 * (b * x) - (1 * 1) := by simp [h₁₃]
          let h₁₅ : b^(m + 1) - 1 = (b - 1) * (b * x + 1) := Eq.trans h₁₄ (Eq.symm (foil_sub_add b 1 (b * x) 1))

          let h₀ : (b - 1) * (b * x + 1) = b^(m + 1) - 1 := Eq.symm h₁₅
          ⟨b * x + 1, h₀⟩
        )
        n
