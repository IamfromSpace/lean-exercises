inductive Vector (α : Type u) : Nat → Type u
  | nil  : Vector α 0
  | cons : α → {n : Nat} → Vector α n → Vector α (n+1)

#check congrArg
#check Vector.rec
#check Vector.casesOn
#check Nat.noConfusion
#check Nat.noConfusionType
#check Vector.noConfusion
#check Vector.noConfusionType
#check Eq.rec

def vec_swap_length
    {α : Type u}
    {n m : Nat}
    (h : n = m)
    (as : Vector α n)
  : Vector α m
  :=
    Eq.rec
      (motive := λ x (_: n = x) ↦ Vector α x)
      as
      h

def vec_append.{u}
    {α : Type u}
    {n m : Nat}
    (as : Vector α n)
    (bs : Vector α m)
  : Vector α (n + m)
  :=
    match n, m, as, bs with
      | _, _, Vector.nil, Vector.nil => Vector.nil
      | _, _, as', Vector.nil => as'
      | _, _, Vector.nil, bs' => vec_swap_length (by simp) bs'
      | k + 1, m, Vector.cons a as', bs' =>
          let h1 : m + 1 = 1 + m := by rw [Nat.add_comm]
          let h2 : k + m + 1 = k + (1 + m) := congrArg (λ x ↦ k + x) h1
          let h3 : k + m + 1 = k + 1 + m := by rw [h2, Nat.add_assoc]
          vec_swap_length h3 (Vector.cons a (vec_append as' bs'))
