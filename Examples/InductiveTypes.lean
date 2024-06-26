#check List.rec
#check List.nil
#check Eq.subst
#check congrArg

theorem append_nil (as : List α) : List.append as List.nil = as :=
  let nil_appended_to_nil_is_nil : List.append List.nil List.nil = List.nil := Eq.refl _

  List.rec
    (motive := λ xs ↦ List.append xs List.nil = xs)
    nil_appended_to_nil_is_nil
    (λ x xs (ih : List.append xs List.nil = xs) ↦
      let cons_outside : x :: (List.append xs List.nil) = x :: xs :=
        congrArg (λ ys ↦ x :: ys) ih

      Eq.subst (motive := λ h ↦ h = x :: xs) (List.cons_append x xs List.nil) cons_outside
    )
    as

theorem cons_append_append (a : α) (as bs cs : List α)
        : List.append (List.append (a :: as) bs) cs = a :: List.append (List.append as bs) cs :=
        -- The long way is that we can apply cons_append twice
        by simp

theorem append_assoc (as bs cs : List α)
        : List.append (List.append as bs) cs = List.append as (List.append bs cs) :=
  let base_left : List.append (List.append [] bs) cs = List.append bs cs :=
    Eq.subst
      (motive := λ xs ↦ List.append xs cs = List.append bs cs)
      (Eq.symm (List.nil_append bs))
      (Eq.refl _)

  let base : List.append (List.append [] bs) cs = List.append [] (List.append bs cs) :=
    Eq.subst
      (motive := λ xs ↦ List.append (List.append [] bs) cs = xs)
      (Eq.symm (List.nil_append (List.append bs cs)))
      base_left

  List.rec
    (motive := λ xs ↦ List.append (List.append xs bs) cs = List.append xs (List.append bs cs))
    base
    (λ x xs (ih : List.append (List.append xs bs) cs = List.append xs (List.append bs cs)) ↦
      let h_x_outside : x :: List.append (List.append xs bs) cs = x :: List.append xs (List.append bs cs) :=
        congrArg (λ ys ↦ x :: ys) ih

      let h_right_fixed : x :: List.append (List.append xs bs) cs = List.append (x :: xs) (List.append bs cs) :=
        Eq.subst
          (motive := λ sub ↦ x :: List.append (List.append xs bs) cs = sub)
          (Eq.symm (List.cons_append x xs (List.append bs cs)))
          h_x_outside

      let h_both_fixed : List.append (List.append (x :: xs) bs) cs = List.append (x :: xs) (List.append bs cs) :=
        Eq.subst
          (motive := λ sub ↦ sub = List.append (x :: xs) (List.append bs cs))
          (Eq.symm (cons_append_append x xs bs cs))
          h_right_fixed

      h_both_fixed
    )
    as

/-
  Eq.rec.{u, u_1}
    {α : Sort u_1}
    {a_left : α}
    {motive : (a : α) → a_left = a → Sort u}
    (refl : motive a_left (_ : a_left = a_left))
    {a_right : α}
    (t : a_left = a_right)
  : motive a_right t
-/

theorem trans {α : Type u} {a b c : α} (h₁ : a = b) (h₂ : b = c) : a = c :=
  Eq.rec
    (motive := λ x _ ↦ a = x)
    h₁
    h₂

theorem myCongrArg.{u} {α β : Sort u} {a b : α} (f : α → β) (h : a = b) : (f a) = (f b) :=
  Eq.rec
    (motive := λ x _ ↦ f a = f x)
    (Eq.refl (f a))
    h

#check congrFun
#check congr

theorem myCongrFun.{u, v} {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x} (h : f = g) (a : α) : f a = g a :=
  Eq.rec
    (motive := λ x _ ↦ f a = x a)
    (Eq.refl (f a))
    h

theorem myCongr.{u, v} {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α} (h₁ : f₁ = f₂) (h₂ : a₁ = a₂) : f₁ a₁ = f₂ a₂ :=
  let ha₁ : f₁ a₁ = f₂ a₁ :=
    Eq.rec
      (motive := λ x _ ↦ f₁ a₁ = x a₁)
      (Eq.refl (f₁ a₁))
      h₁
  Eq.rec
    (motive := λ x _ ↦ f₁ a₁ = f₂ x)
    ha₁
    h₂


#check List.rec

@[simp] def length.{u} {α : Type u} (as : List α) : Nat :=
  match as with
    | List.nil => 0
    | List.cons _ t => 1 + length t

@[simp] theorem cons_adds_len_1.{u}
    {α : Type u}
    (a : α)
    (as : List α)
  : (length (List.cons a as) = 1 + (length as))
  :=
    rfl

@[simp] theorem append_is_length_preserving.{u} {α : Type u} (as bs : List α) : ((length as + length bs) = length (List.append as bs)) :=
  List.rec
    (motive := λ xs ↦ (length xs + length bs) = length (List.append xs bs))
    (by simp : length [] + length bs = length (List.append [] bs))
    (λ a as' (h1 : length as' + length bs = length (List.append as' bs)) ↦
      let h2 : 1 + (length as' + length bs) = 1 + length (List.append as' bs) :=
        by rw [h1]

      let h3 : 1 + length (List.append as' bs) = 1 + (length as' + length bs) :=
        Eq.symm h2

      let h4 : 1 + length (List.append as' bs) = (1 + length as') + length bs :=
        by rw [h3, Nat.add_assoc]

      let h5 : 1 + length (List.append as' bs) = length (a::as') + length bs :=
        by rw [h4, cons_adds_len_1 a as']

      let h6 : length (a::as') + length bs = 1 + length (List.append as' bs) :=
        Eq.symm h5

      let h7 : length (a::as') + length bs = length (a::(List.append as' bs)) :=
        by rw [h6, cons_adds_len_1 a (List.append as' bs)]

      Eq.subst
        (motive := λ sub ↦ length (a::as') + length bs = length sub)
        (Eq.symm (List.cons_append a as' bs))
        h7
    )
    as

@[simp] theorem append_one_adds_len_1.{u}
    {α : Type u}
    (a : α)
    (as : List α)
  : length (List.append as [a]) = 1 + length as
  :=
    calc
      length (List.append as [a]) = length as + length [a] := by rw [append_is_length_preserving]
      _                           = 1 + length as := by simp; rw [Nat.add_comm]

@[simp] theorem append_one_to_reversed_is_reverse_cons.{u}
    {α : Type u}
    (a : α)
    (as : List α)
  : List.append (List.reverse as) [a] = List.reverse (a::as)
  :=
    by simp

theorem reverse_is_length_preserving.{u} {α : Type u} (as : List α) : length (List.reverse as) = length as :=
  List.rec
    (motive := λ xs ↦ length (List.reverse xs) = length xs)
    (Eq.refl _)
    (λ a as' (h1 : length (List.reverse as') = length as') ↦
      let h2 : 1 + length as' = length (a :: as') := Eq.refl _

      let h3 : 1 + length (List.reverse as') = 1 + length (List.reverse as') := Eq.refl _

      let h4 : 1 + length (List.reverse as') = length (List.append (List.reverse as') [a]) :=
        by rw [h3, Eq.symm (append_one_adds_len_1 a (List.reverse as'))]

      let h4 : 1 + length (List.reverse as') = length (List.reverse (a::as')) :=
        by rw [h4, append_one_to_reversed_is_reverse_cons a as']

      let h5 : 1 + length (List.reverse as') = 1 + length as' := by rw [h1]

      Eq.trans (Eq.trans (Eq.symm h4) h5) h2
    )
    as

theorem double_reverse_is_id.{u} {α : Type u} (as : List α) : as = List.reverse (List.reverse as) :=
  List.rec
    (motive := λ xs ↦ xs = List.reverse (List.reverse xs))
    (Eq.refl _)
    (λ a as' (h : as' = List.reverse (List.reverse as')) ↦
      calc
        a :: as' = a :: List.reverse (List.reverse as') := congrArg (λ ys ↦ a :: ys) h
        _        = List.reverse (List.reverse (a::as')) := by simp
    )
    as


inductive Expr where
  | const : Nat → Expr
  | var : Nat → Expr
  | plus : Expr → Expr → Expr
  | times : Expr → Expr → Expr

@[simp] def eval (f : Nat → Nat) (e : Expr) : Nat :=
  match e with
  | Expr.const n => n
  | Expr.var n => f n
  | Expr.plus a b => eval f a + eval f b
  | Expr.times a b => eval f a * eval f b

@[simp] def simpConst (expr : Expr) : Expr :=
  match expr with
    | Expr.plus (Expr.const n₁) (Expr.const n₂)  => Expr.const (n₁ + n₂)
    | Expr.times (Expr.const n₁) (Expr.const n₂) => Expr.const (n₁ * n₂)
    | e                                          => e

@[simp] def fuse (expr : Expr) : Expr :=
  match expr with
    | Expr.plus a b   => simpConst (Expr.plus (fuse a) (fuse b))
    | Expr.times a b  => simpConst (Expr.times (fuse a) (fuse b))
    | e               => e

#check Expr.rec
#check Expr.casesOn

theorem simpConst_eq (v : Nat → Nat)
        : ∀ e : Expr, eval v (simpConst e) = eval v e :=
  λ expr ↦
    -- There must be a better way, lol
    match expr with
      | Expr.plus (Expr.const n₁) (Expr.const n₂)  =>
          let h1 : n₁ + n₂ = eval v (Expr.plus (Expr.const n₁) (Expr.const n₂)) := by simp
          let h2 : eval v (Expr.const (n₁ + n₂)) = n₁ + n₂ := by simp
          let h3 : simpConst (Expr.plus (Expr.const n₁) (Expr.const n₂)) = Expr.const (n₁ + n₂) := by simp
          -- wrap both sides of h3 in eval, and then just compose
          Eq.trans (Eq.trans (congrArg (eval v) h3) h2) h1
      | Expr.plus (Expr.var _) _ =>
          -- We demonstrate that `simpConst (Expr.plus a b) = Expr.plus a b`, then wrap it in eval
          congrArg (eval v) (by simp)
      | Expr.plus (Expr.plus _ _) _ => congrArg (eval v) (by simp)
      | Expr.plus (Expr.times _ _) _ => congrArg (eval v) (by simp)
      | Expr.plus (Expr.const _) (Expr.var _) => congrArg (eval v) (by simp)
      | Expr.plus (Expr.const _) (Expr.plus _ _) => congrArg (eval v) (by simp)
      | Expr.plus (Expr.const _) (Expr.times _ _) => congrArg (eval v) (by simp)
      | Expr.times (Expr.const n₁) (Expr.const n₂) =>
          let h1 : n₁ * n₂ = eval v (Expr.times (Expr.const n₁) (Expr.const n₂)) := by simp
          let h2 : eval v (Expr.const (n₁ * n₂)) = n₁ * n₂ := by simp
          let h3 : simpConst (Expr.times (Expr.const n₁) (Expr.const n₂)) = Expr.const (n₁ * n₂) := by simp
          -- wrap both sides of h3 in eval, and then just compose
          Eq.trans (Eq.trans (congrArg (eval v) h3) h2) h1
      | Expr.times (Expr.var _) _ => congrArg (eval v) (by simp)
      | Expr.times (Expr.plus _ _) _ => congrArg (eval v) (by simp)
      | Expr.times (Expr.times _ _) _ => congrArg (eval v) (by simp)
      | Expr.times (Expr.const _) (Expr.var _) => congrArg (eval v) (by simp)
      | Expr.times (Expr.const _) (Expr.plus _ _) => congrArg (eval v) (by simp)
      | Expr.times (Expr.const _) (Expr.times _ _) => congrArg (eval v) (by simp)
      | Expr.const _ => congrArg (eval v) (by simp)
      | Expr.var _ => congrArg (eval v) (by simp)

theorem fuse_eq (v : Nat → Nat)
        : ∀ e : Expr, eval v (fuse e) = eval v e :=
  Expr.rec
    (motive := λ x ↦ eval v (fuse x) = eval v x)
    (by simp)
    (by simp)
    (λ a b h_a h_b ↦
      calc (eval v (fuse (Expr.plus a b)))
        _ = eval v (simpConst (Expr.plus (fuse a) (fuse b))) := by simp
        _ = eval v (Expr.plus (fuse a) (fuse b)) := by rw [simpConst_eq]
        _ = eval v (fuse a) + eval v (fuse b) := by simp
        _ = eval v a + eval v b := by rw [h_a, h_b]
        _ = eval v (Expr.plus a b) := by simp
    )
    (λ a b h_a h_b ↦
      calc (eval v (fuse (Expr.times a b)))
        _ = eval v (simpConst (Expr.times (fuse a) (fuse b))) := by simp
        _ = eval v (Expr.times (fuse a) (fuse b)) := by rw [simpConst_eq]
        _ = eval v (fuse a) * eval v (fuse b) := by simp
        _ = eval v a * eval v b := by rw [h_a, h_b]
        _ = eval v (Expr.times a b) := by simp
    )
