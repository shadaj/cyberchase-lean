import Mathlib.Tactic.ModCases

mutual
def squadWin (dragons: Nat): Bool :=
  if dragons = 0 then
    True
  else if dragons = 1 then
    False
  else match (dragons - 1) % 4 with
    | 0 => ¬ (hackerWin (dragons - 1))
    | 1 => ¬ (hackerWin (dragons - 1))
    | 2 => ¬ (hackerWin (dragons - 2))
    | 3 => ¬ (hackerWin (dragons - 3))
    | _ => False

def hackerWin (dragons: Nat): Bool :=
  if dragons ≥ 3 then
    ¬(squadWin (dragons - 3)) ∨ ¬(squadWin (dragons - 2)) ∨ ¬(squadWin (dragons - 1))
  else if dragons = 2 then
    ¬(squadWin (dragons - 2)) ∨ ¬(squadWin (dragons - 1))
  else if dragons = 1 then
    ¬(squadWin (dragons - 1))
  else
    True
end

theorem neZeroImpliesGtZero (n: Nat): n ≠ 0 → n > 0 := by
intro h
cases n with
| zero => contradiction
| succ n' => simp

def winCondition (dragons: Nat): Bool :=
  (dragons = 0) ∨ (dragons - 1) % 4 ≠ 0

theorem weWin (dragons: Nat): (winCondition dragons ↔ squadWin dragons) ∧ (winCondition dragons ↔ hackerWin dragons) := by
induction' dragons using Nat.strong_induction_on with d hd

have squadProof: winCondition d ↔ squadWin d :=
  have hd_right_core: ∀ m < d, ¬(winCondition m) ↔ ¬(hackerWin m) := by
    intro x; intro x_lt_d
    apply hd at x_lt_d
    tauto

  have hd_right: ∀ m < d, ¬(winCondition m) → ¬(hackerWin m) := by
    intro x; intro x_lt_d
    exact Iff.mp (hd_right_core x x_lt_d)

  have hd_right_neg: ∀ m < d, (winCondition m) → (hackerWin m) := by
    intro x; intro x_lt_d
    contrapose
    exact Iff.mpr (hd_right_core x x_lt_d)

  Iff.intro
    (fun h: winCondition d => show squadWin d by
      rw [winCondition] at h
      rw [squadWin]
      split

      trivial

      rename_i d_ne_zero
      split
      rename_i d_eq_one
      rw [d_eq_one] at h
      contradiction

      mod_cases (d - 1) % 4

      -- d - 1 = 0 (mod 4)
      rw [H] at h
      simp at h
      contradiction -- H contradicts win state

      -- d - 1 = 1 (mod 4)
      rw [H]; simp

      have d_m_one_neq_zero: (¬d - 1 = 0) = true := by
        apply neZeroImpliesGtZero at d_ne_zero
        simp
        intro a
        rw [a] at H
        contradiction

      have hacker_not_win: ¬(winCondition (d - 1)) := by
        rw [winCondition]
        simp [d_m_one_neq_zero] -- eliminates d = 0 case in h

        have next_d_mod_four: ((d - 1 - 1) % 4) = 0 := by
          cases d with
          | zero => contradiction
          | succ dm1 => cases dm1 with
            | zero => contradiction
            | succ dm2 =>
              rw [← Nat.zero_mod 4, ← Nat.ModEq]
              simp at H
              apply Nat.ModEq.add_right_cancel (Nat.ModEq.refl 1) at H
              exact H
        exact next_d_mod_four

      apply hd_right (d - 1) at hacker_not_win
      simp at hacker_not_win
      exact hacker_not_win
      apply neZeroImpliesGtZero at d_ne_zero
      simp [d_ne_zero]

      -- d - 1 = 2 (mod 4)
      rw [H]; simp

      have d_m_two_neq_zero: (¬d - 2 = 0) = true := by
        simp; intro p
        have d_eq_two: d = 2 := by
          cases d with
          | zero => contradiction
          | succ dm1 => cases dm1 with
            | zero => contradiction
            | succ dm2 => simp; exact p
        rw [d_eq_two] at H; tauto

      have hacker_not_win: ¬(winCondition (d - 2)) := by
        rw [winCondition]
        simp [d_m_two_neq_zero] -- eliminates d = 0 case in h

        have next_d_mod_four: (((d - 2) - 1) % 4) = 0 := by
          cases d with
          | zero => contradiction
          | succ dm1 => cases dm1 with
            | zero => contradiction
            | succ dm2 => cases dm2 with
              | zero => contradiction
              | succ dm3 =>
                rw [← Nat.zero_mod 4, ← Nat.ModEq]
                simp at H
                apply Nat.ModEq.add_right_cancel (Nat.ModEq.refl 2) at H
                exact H
        exact next_d_mod_four

      apply hd_right (d - 2) at hacker_not_win
      simp at hacker_not_win
      exact hacker_not_win
      apply neZeroImpliesGtZero at d_ne_zero
      simp [d_ne_zero]

      -- d - 1 = 3 (mod 4)
      rw [H]; simp

      have d_m_three_neq_zero: (¬d - 3 = 0) = true := by
        simp; intro p
        have d_eq_three: d = 3 := by
          cases d with
          | zero => contradiction
          | succ dm1 => cases dm1 with
            | zero => contradiction
            | succ dm2 => cases dm2 with
              | zero => contradiction
              | succ dm3 => simp; exact p
        rw [d_eq_three] at H; tauto

      have hacker_not_win: ¬(winCondition (d - 3)) := by
        rw [winCondition]
        simp [d_m_three_neq_zero] -- eliminates d = 0 case in h

        have next_d_mod_four: (((d - 3) - 1) % 4) = 0 := by
          cases d with
          | zero => contradiction
          | succ dm1 => cases dm1 with
            | zero => contradiction
            | succ dm2 => cases dm2 with
              | zero => contradiction
              | succ dm3 => cases dm3 with
                | zero => contradiction
                | succ dm4 =>
                  simp only [Nat.reduceSubDiff, add_tsub_cancel_right]
                  rw [← Nat.zero_mod 4, ← Nat.ModEq]
                  rw [add_tsub_cancel_right] at H
                  apply Nat.ModEq.add_right_cancel (Nat.ModEq.refl 3) at H
                  exact H
        exact next_d_mod_four

      apply hd_right (d - 3) at hacker_not_win
      simp at hacker_not_win
      exact hacker_not_win
      apply neZeroImpliesGtZero at d_ne_zero
      simp [d_ne_zero]
    )
    (fun h: squadWin d => show winCondition d by
      contrapose h
      rw [winCondition] at h
      rw [squadWin]
      simp at h
      simp [h]
      intro

      have d_m_one_win: winCondition (d - 1) := by
        rw [winCondition]
        simp
        cases d with
        | zero => contradiction
        | succ dm1 => cases dm1 with
          | zero => contradiction
          | succ dm2 =>
            simp
            have dm1_mod_four_eq_zero: ((dm2 + 2 - 1) % 4) = 0 := by
              tauto
            simp at dm1_mod_four_eq_zero
            intro d_mod_four_eq_zero
            rw [← Nat.zero_mod 4] at dm1_mod_four_eq_zero
            rw [← Nat.zero_mod 4, ← Nat.ModEq] at d_mod_four_eq_zero
            apply Nat.ModEq.add_right 1 at d_mod_four_eq_zero
            rw [d_mod_four_eq_zero] at dm1_mod_four_eq_zero
            simp at dm1_mod_four_eq_zero

      apply hd_right_neg (d - 1) at d_m_one_win
      exact d_m_one_win
      cases d with
      | zero => contradiction
      | succ dm1 => tauto
    )

have hackerProof: winCondition d ↔ hackerWin d :=
  have hd_left_core: ∀ m < d, (winCondition m) ↔ (squadWin m) := by
    intro x; intro x_lt_d
    apply hd at x_lt_d
    tauto

  have hd_left: ∀ m < d, (winCondition m) → (squadWin m) := by
    intro x; intro x_lt_d
    exact Iff.mp (hd_left_core x x_lt_d)

  have hd_left_neg: ∀ m < d, ¬(winCondition m) → ¬(squadWin m) := by
    intro x; intro x_lt_d
    apply hd at x_lt_d
    tauto

  Iff.intro
    (fun h: winCondition d => show hackerWin d by
      simp [winCondition] at h
      rw [hackerWin]

      split
      rename_i d_geq_three
      cases d with
      | zero => contradiction -- d = 0
      | succ dm1 => cases dm1 with
        | zero => contradiction -- d = 1
        | succ dm2 => cases dm2 with
          | zero => contradiction -- d = 2
          | succ dm3 => cases dm3 with
            | zero => simp; nth_rewrite 2 [squadWin]; simp -- d = 3
            | succ dm4 => -- d > 3
              simp

              mod_cases (dm4 + 3) % 4 -- split on d - 1 mod 4
              -- d - 1 = 0 (mod 4)
              simp at h
              contradiction

              -- d - 1 = 1 (mod 4), Hacker wins by taking 1 dragon
              have poison: ¬(winCondition (dm4 + 4 - 1)) := by
                simp [winCondition]
                have x: Nat.ModEq 4 (dm4 + 4 - 1) (1) := by
                  simp; exact H
                apply Nat.ModEq.add_right_cancel (Nat.ModEq.refl 1) at x
                exact x
              apply hd_left_neg (dm4 + 4 - 1) (by simp) at poison
              simp at poison
              simp [poison]

              -- d - 1 = 2 (mod 4), Hacker wins by taking 2 dragons
              have poison: ¬(winCondition (dm4 + 4 - 2)) := by
                simp [winCondition]
                have x: Nat.ModEq 4 (dm4 + 4 - 1) (2) := by
                  simp; exact H
                apply Nat.ModEq.add_right_cancel (Nat.ModEq.refl 2) at x
                exact x
              apply hd_left_neg (dm4 + 4 - 2) (by simp) at poison
              simp at poison
              simp [poison]

              -- d - 1 = 3 (mod 4), Hacker wins by taking 3 dragons
              have poison: ¬(winCondition (dm4 + 4 - 3)) := by
                simp [winCondition]
                have x: Nat.ModEq 4 (dm4 + 4 - 1) (3) := by
                  simp; exact H
                apply Nat.ModEq.add_right_cancel (Nat.ModEq.refl 3) at x
                exact x
              apply hd_left_neg (dm4 + 4 - 3) (by simp) at poison
              simp at poison
              simp [poison]

      split
      rename_i d_eq_two
      simp [d_eq_two, squadWin]

      split
      rename_i d_eq_one
      rw [d_eq_one] at h
      contradiction

      trivial)
    (fun h: hackerWin d => show winCondition d by
      contrapose h
      rw [winCondition] at h
      rw [hackerWin]
      simp at h
      simp [h]
      split
      rename_i d_geq_three
      simp

      have zero_equiv_four: Nat.ModEq 4 0 4 := by
        tauto

      have d_m_one_equiv_0: Nat.ModEq 4 (d - 1) 0 := by
        apply And.right at h
        rw [← Nat.zero_mod 4, ← Nat.ModEq] at h
        exact h

      have d_minus_three_win: winCondition (d - 3) := by
        rw [winCondition]
        by_cases d - 3 = 0

        rename_i d_m_three_eq_zero
        rw [d_m_three_eq_zero]; tauto

        rename_i d_m_three_neq_zero
        simp [d_m_three_neq_zero]
        cases d with
        | zero => contradiction
        | succ dm1 => cases dm1 with
          | zero => contradiction
          | succ dm2 => cases dm2 with
            | zero => contradiction
            | succ dm3 => cases dm3 with
              | zero => contradiction
              | succ dm4 =>
                simp
                simp at h
                rw [← Nat.zero_mod 4, ← Nat.ModEq] at h
                apply Nat.ModEq.trans h at zero_equiv_four
                apply Nat.ModEq.add_right_cancel (Nat.ModEq.refl 3) at zero_equiv_four
                rw [zero_equiv_four]
                simp
      have d_minus_two_win: winCondition (d - 2) := by
        rw [winCondition]
        simp
        by_cases d - 2 = 0
        rename_i d_m_two_eq_zero
        tauto
        rename_i d_m_two_neq_zero
        simp [d_m_two_neq_zero]
        cases d with
        | zero => contradiction
        | succ dm1 => cases dm1 with
          | zero => contradiction
          | succ dm2 => cases dm2 with
            | zero => contradiction
            | succ dm3 =>
              simp
              simp at h
              rw [← Nat.zero_mod 4, ← Nat.ModEq] at h
              apply Nat.ModEq.trans h at zero_equiv_four
              apply Nat.ModEq.add_right_cancel (Nat.ModEq.refl 2) at zero_equiv_four
              rw [zero_equiv_four]
              simp
      have d_minus_one_win: winCondition (d - 1) := by
        rw [winCondition]
        simp
        by_cases d - 1 = 0
        rename_i d_m_one_eq_zero
        tauto
        rename_i d_m_one_neq_zero
        simp [d_m_one_neq_zero]
        cases d with
        | zero => contradiction
        | succ dm1 => cases dm1 with
          | zero => contradiction
          | succ dm2 =>
            simp
            simp at h
            rw [← Nat.zero_mod 4, ← Nat.ModEq] at h
            apply Nat.ModEq.trans h at zero_equiv_four
            apply Nat.ModEq.add_right_cancel (Nat.ModEq.refl 1) at zero_equiv_four
            rw [zero_equiv_four]
            simp

      have zero_lt_d: 0 < d := by
        cases d with
        | zero => contradiction
        | succ dm1 => simp

      have squad_win_three: squadWin (d - 3) := by
        apply hd_left (d - 3) at d_minus_three_win
        exact d_minus_three_win
        simp [d_geq_three]
        exact zero_lt_d

      have squad_win_two: squadWin (d - 2) := by
        apply hd_left (d - 2) at d_minus_two_win
        exact d_minus_two_win
        simp [d_geq_three]
        exact zero_lt_d

      have squad_win_one: squadWin (d - 1) := by
        apply hd_left (d - 1) at d_minus_one_win
        exact d_minus_one_win
        simp [d_geq_three]
        exact zero_lt_d
      tauto

      rename_i d_lt_three
      split
      rename_i d_eq_two
      rw [d_eq_two] at h
      contradiction

      rename_i d_neq_two
      have d_eq_one: d = 1 := by
        cases d with
        | zero => contradiction -- d = 0
        | succ dm1 => cases dm1 with
          | zero => tauto -- d = 1
          | succ dm2 => cases dm2 with
            | zero => contradiction -- d = 2
            | succ dm3 => simp at d_lt_three -- d >= 3

      simp [d_eq_one]
      rw [squadWin]; tauto
    )

tauto
