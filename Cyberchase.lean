import Mathlib.Data.Nat.Cast.Order.Ring
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

theorem neZeroImpliesGtZero (n: Nat): n ≠ 0 → n > 0 := by omega

def winCondition (dragons: Nat): Bool :=
  (dragons = 0) ∨ (dragons - 1) % 4 ≠ 0

lemma dm1_eq_k_means_d_neq_k {d k : Nat} (H : (d - 1) % 4 = k) (k_ne_zero : k ≠ 0) : d - k ≠ 0 := by omega

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

      have d_gt_zero: d > 0 := by
        apply neZeroImpliesGtZero at d_ne_zero
        exact d_ne_zero

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

      have hacker_not_win: ¬(winCondition (d - 1)) := by
        rw [winCondition]
        simp [dm1_eq_k_means_d_neq_k H] -- eliminates d = 0 case in h

        have next_d_mod_four: ((d - 1 - 1) % 4) = 0 := by
          match d with
          | 0 | 1 => contradiction
          | dm2 + 2 =>
            rw [← Nat.zero_mod 4, ← Nat.ModEq]
            simp at H
            apply Nat.ModEq.add_right_cancel (Nat.ModEq.refl 1) at H
            exact H
        exact next_d_mod_four

      apply hd_right (d - 1) (by
        simp [d_gt_zero]
      ) at hacker_not_win
      simp at hacker_not_win
      exact hacker_not_win

      -- d - 1 = 2 (mod 4)
      rw [H]; simp

      have hacker_not_win: ¬(winCondition (d - 2)) := by
        rw [winCondition]
        simp [dm1_eq_k_means_d_neq_k H] -- eliminates d = 0 case in h

        have next_d_mod_four: (((d - 2) - 1) % 4) = 0 := by
          match d with
          | 0 | 1 | 2 => contradiction
          | dm3 + 3 =>
            rw [← Nat.zero_mod 4, ← Nat.ModEq]
            simp at H
            apply Nat.ModEq.add_right_cancel (Nat.ModEq.refl 2) at H
            exact H
        exact next_d_mod_four

      apply hd_right (d - 2) (by
        simp [d_gt_zero]
      ) at hacker_not_win
      simp at hacker_not_win
      exact hacker_not_win

      -- d - 1 = 3 (mod 4)
      rw [H]; simp

      have hacker_not_win: ¬(winCondition (d - 3)) := by
        rw [winCondition]
        simp [dm1_eq_k_means_d_neq_k H] -- eliminates d = 0 case in h

        have next_d_mod_four: (((d - 3) - 1) % 4) = 0 := by
          match d with
          | 0 | 1 | 2 | 3 => contradiction
          | dm4 + 4 =>
            rw [← Nat.zero_mod 4, ← Nat.ModEq]
            simp at H
            apply Nat.ModEq.add_right_cancel (Nat.ModEq.refl 3) at H
            exact H
        exact next_d_mod_four

      apply hd_right (d - 3) (by
        simp [d_gt_zero]
      ) at hacker_not_win
      simp at hacker_not_win
      exact hacker_not_win
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
        omega

      exact hd_right_neg (d - 1) (by omega) d_m_one_win
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
      -- d >= 3
      rename_i d_geq_three
      match d with
      | 0 | 1 | 2 => contradiction
      | 3 => simp; nth_rewrite 2 [squadWin]; simp -- d = 3
      | dm4 + 4 => -- d > 3
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
      -- d == 2
      rename_i d_eq_two
      simp [d_eq_two, squadWin]

      split
      -- d == 1
      rename_i d_eq_one
      rw [d_eq_one] at h
      contradiction

      -- d == 0
      trivial
    )
    (fun h: hackerWin d => show winCondition d by
      contrapose h
      rw [winCondition] at h
      rw [hackerWin]
      simp at h
      simp
      split
      rename_i d_geq_three
      simp

      have squad_win_three: squadWin (d - 3) := by
        exact hd_left (d - 3) (by omega) (by
          rw [winCondition]
          simp
          omega)

      have squad_win_two: squadWin (d - 2) := by
        exact hd_left (d - 2) (by omega) (by
          rw [winCondition]
          simp
          omega)

      have squad_win_one: squadWin (d - 1) := by
        exact hd_left (d - 1) (by omega) (by
          rw [winCondition]
          simp
          omega)
      tauto

      rename_i d_lt_three
      split
      -- d == 2
      rename_i d_eq_two
      rw [d_eq_two] at h
      contradiction

      rename_i d_neq_two
      have d_eq_one: d = 1 := by omega
      simp [d_eq_one]
      rw [squadWin]; decide
    )

tauto
