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
