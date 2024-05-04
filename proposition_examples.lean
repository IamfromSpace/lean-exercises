variable (p q r : Prop)

#check Or.intro_left
#check Or.intro_right
#check Or.elim
#check Iff.intro
#check False.elim

def Or.elim_comp {a b c : Prop} (left : a → c) (right : b → c) (h : a ∨ b) : c := Or.elim h left right

theorem a_and_b_implies_b_and_a (a : Prop) (b : Prop) (hab : a /\ b) : b /\ a :=
  And.intro hab.right hab.left

theorem a_or_b_implies_b_or_a (a : Prop) (b : Prop) : a \/ b -> b \/ a :=
  Or.elim_comp (Or.intro_right b) (Or.intro_left a)


-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (a_and_b_implies_b_and_a p q)
    (a_and_b_implies_b_and_a q p)

example : p ∨ q ↔ q ∨ p :=
  Iff.intro
    (a_or_b_implies_b_or_a p q)
    (a_or_b_implies_b_or_a q p)

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ q ∧ r :=
  let first_group_implies_second_group :=
    fun x : ((p /\ q) /\ r) => And.intro x.left.left (And.intro x.left.right x.right);
  let second_group_implies_first_group :=
    fun x : (p /\ q /\ r) => And.intro (And.intro x.left x.right.left) x.right.right;

  Iff.intro
    first_group_implies_second_group
    second_group_implies_first_group

example : (p ∨ q) ∨ r ↔ p ∨ q ∨ r :=
  let first_group_implies_second_group :=
    Or.elim_comp
      (Or.elim_comp
        (Or.intro_left (q ∨ r))
        (Or.intro_right p ∘ Or.intro_left r)
      )
      (Or.intro_right p ∘ Or.intro_right q)
  let second_group_implies_first_group :=
    Or.elim_comp
      (Or.intro_left r ∘ Or.intro_left q)
      (Or.elim_comp
        (Or.intro_left r ∘ Or.intro_right p)
        (Or.intro_right (p ∨ q))
      )

  Iff.intro
    first_group_implies_second_group
    second_group_implies_first_group


-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  let can_distribute :=
    fun (x : p ∧ (q ∨ r)) =>
      Or.elim x.right
        (Or.intro_left (p /\ r) ∘ And.intro x.left)
        (Or.intro_right (p /\ q) ∘ And.intro x.left)
  let can_extract :=
    Or.elim_comp
      (fun (x : p /\ q) => And.intro x.left (Or.intro_left r x.right))
      (fun (x : p /\ r) => And.intro x.left (Or.intro_right q x.right))

  Iff.intro
    can_distribute
    can_extract

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  let can_distribute :=
    Or.elim_comp
      (fun (x: p) => And.intro (Or.intro_left q x) (Or.intro_left r x))
      (fun (x: q ∧ r) => And.intro (Or.intro_right p x.left) (Or.intro_right p x.right))

  let can_extract :=
    fun (x1: (p ∨ q) ∧ (p ∨ r)) =>
      Or.elim x1.left
        (Or.intro_left (q ∧ r))
        (fun (x2 : q) => 
          Or.elim x1.right
            (Or.intro_left (q ∧ r))
            (Or.intro_right p ∘ And.intro x2)
        )

  Iff.intro
    can_distribute
    can_extract


-- other properties
example : (p → q → r) ↔ (p ∧ q → r) :=
  let lr :=
    fun (hpqr : p → q → r) (hpq : p ∧ q) => hpqr hpq.left hpq.right
  let rl :=
    fun (hpqr : p ∧ q → r) (hp : p) => hpqr ∘ And.intro hp

  Iff.intro lr rl

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  let can_distribute :=
    fun (hpqr : (p ∨ q) → r) =>
      And.intro
        (hpqr ∘ Or.intro_left q)
        (hpqr ∘ Or.intro_right p)
  let can_extract :=
    fun (hprqr : (p → r) ∧ (q → r)) =>
      Or.elim_comp hprqr.left hprqr.right

  Iff.intro
    can_distribute
    can_extract

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  let lr :=
    fun (hpq : ¬(p ∨ q)) =>
      And.intro
        (hpq ∘ Or.intro_left q)
        (hpq ∘ Or.intro_right p)
  let rl :=
    fun (h : ¬p ∧ ¬q) =>
      Or.elim_comp h.left h.right

  Iff.intro lr rl

example : ¬p ∨ ¬q → ¬(p ∧ q) :=
  fun (h : ¬p ∨ ¬q) (h2 : p ∧ q) =>
    Or.elim h
      (fun (h3 : ¬p) => h3 h2.left)
      (fun (h3 : ¬q) => h3 h2.right)

example : ¬(p ∧ ¬p) :=
  fun (h : p /\ ¬p) => h.right h.left

example : p ∧ ¬q → ¬(p → q) :=
  fun (h1 : p ∧ ¬q) (h2 : p → q) => h1.right (h2 (h1.left))

example : ¬p → (p → q) :=
  fun (h : ¬p) => False.elim ∘ h

example : (¬p ∨ q) → (p → q) :=
  fun (h : ¬p ∨ q) (hp : p) =>
    Or.elim h
      (fun (hnp : ¬p) => False.elim (hnp hp))
      id

example : p ∨ False ↔ p :=
  Iff.intro
    (Or.elim_comp id False.elim)
    (Or.intro_left False)

example : p ∧ False ↔ False :=
  Iff.intro
    And.right
    (fun x => And.intro (False.elim x) x)

example : (p → q) → (¬q → ¬p) :=
  -- Literally just flipped function composition!
  fun (h : p → q) (hnq : ¬q) => hnq ∘ h

#check Iff.mp
#check Iff.mpr
#check Iff
#check absurd

def const (x: a) (_: b) : a := x

-- classical theorems
example : (p → q ∨ r) → ((p → q) ∨ (p → r)) :=
  fun (h : p → q ∨ r) =>
    Or.elim (Classical.em p)
      (Or.elim_comp
        (Or.intro_left (p -> r) ∘ const)
        (Or.intro_right (p -> q) ∘ const)
        ∘
        h)
      (fun hnp : (p -> False) => Or.intro_left (p -> r) (False.elim ∘ hnp))

example : ¬(p ∧ q) → ¬p ∨ ¬q :=
  fun (h : ¬(p ∧ q)) =>
    Or.elim (Classical.em p)
      (fun (hp : p) =>
        Or.elim (Classical.em q)
          (False.elim ∘ h ∘ And.intro hp)
          (Or.intro_right (¬p))
      )
      (Or.intro_left (¬q))

theorem impl_associativity {a b c : Prop} (f : (a → b) → c) (_ : a) (y : b) : c :=
  f (const y)

example : ¬(p → q) → p ∧ ¬q :=
  fun (p_does_not_imply_q : ¬(p → q)) =>
    Or.elim (Classical.em p)
      (fun (hp : p) =>
        let p_implies_not_q := impl_associativity p_does_not_imply_q
        And.intro hp (p_implies_not_q hp)
      )
      (fun (hnp : ¬p) =>
        let p_implies_q := False.elim ∘ hnp
        absurd p_implies_q p_does_not_imply_q
      )

example : (p → q) → (¬p ∨ q) :=
  fun (h : p → q) =>
    Or.elim (Classical.em p)
      (Or.intro_right (¬p) ∘ h)
      (Or.intro_left q)

example : (¬q → ¬p) → (p → q) :=
  fun (h : ¬q → ¬p) =>
    Or.elim (Classical.em q)
      const
      (fun (hnq : ¬q) => False.elim ∘ h hnq)

example : p ∨ ¬p :=
  Classical.em p

example : (((p → q) → p) → p) :=
  fun (h : (p → q) → p) =>
    Or.elim (Classical.em p)
      id
      (fun (hnp : ¬p) => h (False.elim ∘ hnp))


theorem double_implies {a : Prop} (f : a -> a -> b) : a -> b :=
  fun (h : a) => f h h

-- without classical challenge
example : ¬(p ↔ ¬p) :=
  fun (h : p ↔ ¬p) =>
    let hnp := double_implies h.mp
    absurd
      (h.mpr hnp)
      hnp
