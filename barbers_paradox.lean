variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

theorem p_implies_not_p_proves_not_p
  {p : Prop}
  (h : p → ¬p)
    : ¬p :=
      (λ hp ↦ (h hp) hp)

theorem p_iff_not_p_is_false
  {p : Prop}
  (h : p ↔ ¬p)
    : False :=
      let hnp := p_implies_not_p_proves_not_p h.mp
      let hp := h.mpr hnp
      hnp hp

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False :=
  p_iff_not_p_is_false (h barber)
