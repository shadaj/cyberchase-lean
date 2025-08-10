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

lemma generic_hacker_not_win {d k : Nat} (H: d - 1 ≡ k [MOD 4]) (k_lt_d: k < d) (km4_eq_k : k % 4 = k) (k_ne_zero : k ≠ 0) : ¬(winCondition (d - k)) := by
  let dmk := d - k - 1
  have dmk_eq : dmk + k + 1 = d := by omega
  have dmk_eq_rev : dmk = d - k - 1 := by omega

  rw [winCondition]
  simp [dm1_eq_k_means_d_neq_k (by
    rw [H]; simp [km4_eq_k]
  ) k_ne_zero] -- eliminates d = 0 case in h

  have next_d_mod_four: (((d - k) - 1) % 4) = 0 := by
    rw [← dmk_eq] at H
    rw [← Nat.zero_mod 4, ← Nat.ModEq]
    simp at H
    rw (occs := .pos [2]) [← Nat.add_zero (k)] at H
    rw (occs := .pos [2]) [← Nat.add_comm] at H
    apply Nat.ModEq.add_right_cancel (Nat.ModEq.refl k) at H
    rw [dmk_eq_rev] at H
    exact H
  exact next_d_mod_four

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

      -- d == 0
      trivial

      split
      -- d == 1
      rename_i d_eq_one
      rw [d_eq_one] at h
      contradiction

      -- d > 1
      by_cases (d - 1) % 4 = 0

      -- d - 1 = 0 (mod 4)
      rename_i H
      rw [H] at h
      simp at h
      contradiction -- H contradicts win state

      -- d - 1 = k (mod 4), k > 0
      have ⟨k, hk⟩ : ∃ k ≠ 0, k % 4 = k ∧ (d - 1) % 4 = k := by
        use (d - 1) % 4
        omega
      have H : d - 1 ≡ k [MOD 4] := by
        have a : (d - 1) % 4 = k := by
          tauto
        have b : k % 4 = k := by
          tauto
        rw [← b] at a
        exact a
      rw [H]; simp [hk]

      have hacker_not_win: ¬(winCondition (d - k)) :=
        generic_hacker_not_win (H) (by omega) (by simp [hk]) (by simp [hk])

      apply hd_right (d - k) (by
        omega
      ) at hacker_not_win
      simp at hacker_not_win

      match k with
      | 1 | 2 | 3 => simp; exact hacker_not_win
      | _ + 4 => omega -- cannot happen because k % 4 = k
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

      -- d >= 3
      match d with
      | 0 => trivial
      | 1 => contradiction
      | 2 => simp [squadWin]
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
          tauto

          -- d - 1 = 2 (mod 4), Hacker wins by taking 2 dragons
          have poison: ¬(winCondition (dm4 + 4 - 2)) := by
            simp [winCondition]
            have x: Nat.ModEq 4 (dm4 + 4 - 1) (2) := by
              simp; exact H
            apply Nat.ModEq.add_right_cancel (Nat.ModEq.refl 2) at x
            exact x
          apply hd_left_neg (dm4 + 4 - 2) (by simp) at poison
          simp at poison
          tauto

          -- d - 1 = 3 (mod 4), Hacker wins by taking 3 dragons
          have poison: ¬(winCondition (dm4 + 4 - 3)) := by
            simp [winCondition]
            have x: Nat.ModEq 4 (dm4 + 4 - 1) (3) := by
              simp; exact H
            apply Nat.ModEq.add_right_cancel (Nat.ModEq.refl 3) at x
            exact x
          apply hd_left_neg (dm4 + 4 - 3) (by simp) at poison
          simp at poison
          tauto
    )
    (fun h: hackerWin d => show winCondition d by
      contrapose h
      rw [winCondition] at h
      rw [hackerWin]
      simp at h
      simp
      split
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
