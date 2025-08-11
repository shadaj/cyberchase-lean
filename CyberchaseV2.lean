import Mathlib.Tactic.ModCases

mutual
def squadWins (green_dragons: Nat): Bool :=
  if green_dragons = 0 then
    False
  else
    if green_dragons % 4 = 0 then
      ¬ hackerWins (green_dragons - 1)
    else
      ¬ hackerWins (green_dragons - (green_dragons % 4))

def hackerWins (green_dragons: Nat): Bool :=
  if green_dragons = 0 then
    False
  else
    ¬(squadWins (green_dragons - 3)) ∨ ¬(squadWins (green_dragons - 2)) ∨ ¬(squadWins (green_dragons - 1))
end

def isPoisonNumber (green_dragons: Nat): Bool :=
  Nat.ModEq 4 green_dragons 0

theorem mod_zero_plus_k { x k n: Nat } (k_lt_n: k < n) (x_congr_zero: Nat.ModEq n x 0): (x + k) % n = k := by
  rw [Nat.ModEq] at x_congr_zero
  nth_rewrite 2 [← Nat.mod_eq_of_lt k_lt_n]
  rw [Nat.add_mod, x_congr_zero]; simp

theorem poison_number_for_hacker (green_dragons: Nat) (h: isPoisonNumber green_dragons): ¬ hackerWins green_dragons := by
  induction' green_dragons using Nat.strong_induction_on with green_dragons hd

  simp [isPoisonNumber] at h
  unfold hackerWins
  split

  -- green_dragons = 0
  simp

  -- green_dragons > 0
  match green_dragons with
  | 0 => contradiction
  | 1 => contradiction
  | 2 => contradiction
  | 3 => contradiction
  | next_poison + 4 =>
    unfold squadWins; simp
    have next_poison_mod_4: next_poison ≡ 0 [MOD 4] := by
      have mod_4_eq_zero: 4 ≡ 0 [MOD 4] := by
        simp [Nat.ModEq]
      exact Nat.ModEq.add_right_cancel mod_4_eq_zero h

    rw [
      mod_zero_plus_k (by decide) next_poison_mod_4,
      mod_zero_plus_k (by decide) next_poison_mod_4,
      mod_zero_plus_k (by decide) next_poison_mod_4
    ]
    simp

    have nextIsPoison: isPoisonNumber next_poison := by
      unfold isPoisonNumber; simp
      exact next_poison_mod_4

    apply hd next_poison (by simp) at nextIsPoison
    simp at nextIsPoison
    exact nextIsPoison

theorem non_poison_squad_win (green_dragons: Nat) (h: ¬ isPoisonNumber green_dragons): squadWins green_dragons := by
  unfold isPoisonNumber at h; simp at h
  unfold squadWins; simp

  have green_dragons_nonzero: green_dragons ≠ 0 := by
    intro zero_dragon
    rw [zero_dragon] at h
    contradiction

  simp [green_dragons_nonzero]
  split
  contradiction -- green_dragons % 4 = 0 (but that is poison)

  have hacker_given_poison: (green_dragons - (green_dragons % 4)) % 4 = 0 :=
    by omega
  have hackerLoses := poison_number_for_hacker (green_dragons - (green_dragons % 4)) (by
    unfold isPoisonNumber; simp
    rw [Nat.ModEq]; simp
    exact hacker_given_poison
  )
  simp at hackerLoses; exact hackerLoses
