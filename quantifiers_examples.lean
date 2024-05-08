variable (α : Type) (p q : α → Prop) (r : Prop)

#check Exists.intro
#check Exists.elim

example : (∃ _ : α, r) → r :=
  λ h ↦ Exists.elim h (λ _ hr ↦ hr)

/-
  This is substantially less trivial than it seems, because there's a trick at
  play here.  We are not solving:
    r → (∃ _ : α, r)

  Because of the outer parameter.  The outer parameter, in fact, is equivalent
  to a forall statement.  So we're actually proving:
    ∀ x, r → (∃ _ : α, r)

  Note that the former cannot be shown.  This is the case, because the set may
  be empty.  We can't say that there exists some element by which some trivial
  property holds, because we don't know that an element exists!  However, by
  wrapping this in a forall, we have a way out.  The inner statement is true
  for all witnesses, and absence of a witness means that you can never imply
  the inner statement at all.  So if the inner statement is nonsense for the
  empty set, that's fine, because the inner statement is unprovable for the
  empty set.
-/
example (a : α) : r → (∃ _ : α, r) :=
  λ hr ↦ Exists.intro a hr

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
  let can_extract :=
    λ h₁ ↦ Exists.elim h₁ (λ w h₂ ↦ And.intro (Exists.intro w h₂.left) h₂.right)
  let can_embed :=
    λ h₁ ↦ Exists.elim h₁.left (λ w h₂ ↦ Exists.intro w (And.intro h₂ h₁.right))

  Iff.intro
    can_extract
    can_embed

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
  let can_split :=
    λ h₁ ↦ Exists.elim h₁
      (λ w h₂ ↦
        Or.elim h₂
          (Or.intro_left (∃ x, q x) ∘ Exists.intro w)
          (Or.intro_right (∃ x, p x) ∘ Exists.intro w)
      )
  let can_combine :=
    λ h₁ ↦
      Or.elim h₁
        (λ h₂ ↦ Exists.elim h₂ (λ w hpx ↦ Exists.intro w (Or.intro_left _ hpx)))
        (λ h₂ ↦ Exists.elim h₂ (λ w hqx ↦ Exists.intro w (Or.intro_right _ hqx)))

  Iff.intro
    can_split
    can_combine

#check absurd

example : (∀ x, p x) ↔ ¬(∃ x, ¬p x) :=
  let to_existential :=
    λ (h₁ : (x : α) → p x) ↦
      Or.elim (Classical.em (∃ x, ¬p x))
        (λ h₂ ↦ Exists.elim h₂ (λ w hnpx ↦ absurd (h₁ w) hnpx))
        id

  let to_universal :=
    λ (h₁ : (∃ x, p x → False) → False) (x : α) ↦
      Or.elim (Classical.em (p x))
        id
        (λ hnpx ↦ False.elim (h₁ (Exists.intro x hnpx)))

  Iff.intro
    to_existential
    to_universal

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
  let to_universal :=
    λ (h₁ : (∃ x, p x)) ↦
      Exists.elim h₁
        (λ w h₂ all_not_p ↦ absurd h₂ (all_not_p w))

  let to_existential :=
    λ (h₁ : ((x : α) → p x → False) → False) ↦
      Or.elim (Classical.em (∃ x, p x))
        id
        (λ h₂ ↦ False.elim (h₁ (λ w hpx ↦ absurd (Exists.intro w hpx) h₂)))

  Iff.intro
    to_universal
    to_existential

theorem not_exists_px_is_all_not_px.{u} { α' : Sort u } { p' : α' → Prop } : (¬ ∃ x, p' x) → (∀ x, ¬ p' x) :=
  λ (h₁ : (∃ x, p' x) → False) (x : α') ↦
    Or.elim (Classical.em (p' x))
      (λ hpx ↦ absurd (Exists.intro x hpx) h₁)
      id

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
  let to_universal :=
    not_exists_px_is_all_not_px

  let to_existential :=
    λ a b ↦ Exists.elim b a

  Iff.intro
    to_universal
    to_existential

theorem not_all_x_px_implies_exists_x_not_px.{u} {α' : Sort u} {p' : α' → Prop} : (¬ ∀ x, p' x) → (∃ x, ¬p' x) :=
  λ (h₁ : ((x : α') → p' x) → False) ↦
    Or.elim (Classical.em (∃ x, ¬p' x))
      id
      (λ h₂ ↦
        False.elim
          (h₁ (λ (x : α') ↦ 
            Or.elim (Classical.em (p' x))
              id
              (λ hnpx ↦ absurd (Exists.intro x hnpx) h₂)
          ))
      )

example : (¬ ∀ x, p x) ↔ (∃ x, ¬p x) :=
  let to_existential :=
    not_all_x_px_implies_exists_x_not_px

  let to_universal :=
    λ h₁ h₂ ↦
       Exists.elim h₁ (λ w ↦ absurd (h₂ w))

  Iff.intro
    to_existential
    to_universal


example : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
  let to_existential :=
    λ a b ↦ Exists.elim b a

  let to_universal :=
    λ h x ↦ h ∘ Exists.intro x

  Iff.intro
    to_existential
    to_universal


example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
  let to_universal :=
    λ (h₁ : ∃ x, p x → r) (h₂ : (x : α) → p x) ↦
      Exists.elim h₁ (λ w hpxr ↦ hpxr (h₂ w))

  let to_existential :=
    /-
      If eating (p) all pills (α) kills me (r) and there was at least one pill
      (x), it implies that there was at least one pill that, if eaten, would
      kill me
    -/
    λ (h₁ : ((x : α) → p x) → r) ↦
      Or.elim (Classical.em (∀ x, p x))
        (λ h₂ ↦ Exists.intro a (λ (_ : p a) ↦ h₁ h₂))
        (λ hn₂ ↦
          let ⟨w, hnpw⟩ := not_all_x_px_implies_exists_x_not_px hn₂;
          Exists.intro w (False.elim ∘ hnpw)
        )

  Iff.intro
    to_universal
    to_existential

theorem not_p_implies_anything { p' : Prop } { r' : Prop } : (¬p') → (p' → r') :=
  λ (hnp : ¬p') ↦ False.elim ∘ hnp

example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) :=
  let lr :=
    λ (h : ∃ x, r → p x) hr ↦
      Exists.elim h (λ w hrpx ↦ Exists.intro w (hrpx hr))

  /-
    The existential qualifier of the Calculus of Constructors is especially
    strong, because it means we _know_ of an exact witness.  So if we take:
      (r → ∃ x, p x)

    To mean, "If Alice is drunk (r) we know that at least one bottle of wine
    (x) from the cellar (α) is empty (p)," then under set theory, we don't
    really know _which_ bottle, just some particular subset.  However, here we
    actually _learn_ of a witness to this fact, we know an empty bottle
    exactly!  So this is more akin to saying, "If Alice is drunk (r) we know
    that the bottle she's holding (x) is empty (p)."

    This makes our goal statement make a bit more sense:
      (∃ x, r → p x)

    It says something like, "Consider the bottle Alice is holding, if she's
    drunk, you know it's empty."
  -/
  let rl : ∀ _, (r → ∃ x, p x) → (∃ x, r → p x) :=
    λ (a' : α) (h : r → ∃ x, p x) ↦
      Or.elim (Classical.em r)
        (λ hr ↦ Exists.elim (h hr) (λ w hpx ↦ Exists.intro w (λ (_ : r) ↦ hpx)))
        (Exists.intro a' ∘ not_p_implies_anything)


  Iff.intro
    lr
    (rl a)