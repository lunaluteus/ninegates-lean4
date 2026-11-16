/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates.Minimal.Alternating.Defs
public import Ninegates.Meldable.Prefix

/-! The exceptional triplet coefficients depend on only the first five ranks.
Fixed prefix states are checked in the kernel and transported to every order. -/

@[expose] public section

namespace Mahjong.VirtualHand.AlternatingWait

private def prefixValue (k : ℕ) : ℤ :=
  if k = 0 then 2 else if k = 1 then 4 else if k = 2 then 6
  else if k = 3 then 3 else if k = 4 then 3 else 0

private def prefixModel (draw : Fin 6) (q : Fin 3) : VirtualHand 2 :=
  (fun r ↦ prefixValue r.val) + single (n := 2) draw - pair (n := 2) ⟨q.val, by omega⟩

private lemma prefix_certificate (b : Fin 2) (draw : Fin 6) (q : Fin 3)
    (allowed : draw.val = 5 ∨ (draw.val + q.val + b.val) % 3 = 2) :
    0 ≤ canonicalTriplet (prefixModel draw q) 3 ∧
      (b.val = 1 → 0 ≤ canonicalTriplet (prefixModel draw q) 4) := by
  fin_cases b <;> fin_cases draw <;> fin_cases q <;> norm_num at allowed <;> decide +kernel

private lemma early_hand {n : ℕ} (order : 2 ≤ n) (i : Rank n) (early : i.val ≤ 4)
    (four : i.val = 4 → n % 2 = 1) : hand n i = prefixValue i.val := by
  rw [hand_apply]
  unfold prefixValue
  interval_cases position : i.val
  all_goals norm_num
  have not_tail : ¬3 * n ≤ 6 := by have odd := four rfl; omega
  rw [ite_eq_right not_tail, ite_eq_left (four rfl)]

private lemma prefix_eq {n : ℕ} (order : 2 ≤ n) (i q : Rank n) (small : q.val < 3)
    (limit : ℕ) (bound : limit ≤ 4) (odd : limit = 4 → n % 2 = 1) :
    ∀ k ≤ limit, coefficient (hand n + single i - pair q) (k : ℤ) =
      coefficient (prefixModel ⟨min i.val 5, by omega⟩ ⟨q.val, small⟩) (k : ℤ) := by
  intro k before
  let x : Rank n := ⟨k, by omega⟩
  let y : Rank 2 := ⟨k, by omega⟩
  have actual := coefficient_fin (hand n + single i - pair q) x
  have model := coefficient_fin (prefixModel ⟨min i.val 5, by omega⟩ ⟨q.val, small⟩) y
  change coefficient _ (k : ℤ) = _ at actual model
  rw [actual, model]
  simp only [prefixModel, Pi.sub_apply, Pi.add_apply, pair_apply, single_apply, Fin.ext_iff]
  rw [early_hand order x (by dsimp [x]; omega) (by
    intro at_four
    apply odd
    dsimp [x] at at_four
    omega)]
  dsimp only [x, y]
  split_ifs <;> omega

lemma prefix_triplets_nonnegative {n : ℕ} (order : 2 ≤ n) (i q : Rank n) (small : q.val < 3)
    (congruent : (i.val + q.val + n % 2) % 3 = 2) :
    0 ≤ canonicalTriplet (hand n + single i - pair q) ⟨3, by omega⟩ ∧
      (n % 2 = 1 → 0 ≤ canonicalTriplet (hand n + single i - pair q) ⟨4, by omega⟩) := by
  have allowed : min i.val 5 = 5 ∨ (min i.val 5 + q.val + n % 2) % 3 = 2 := by
    by_cases early : i.val < 5
    · right
      have minimum : min i.val 5 = i.val := Nat.min_eq_left (by omega)
      simpa only [minimum] using congruent
    · left
      omega
  have certificate := prefix_certificate ⟨n % 2, by omega⟩
    ⟨min i.val 5, by omega⟩ ⟨q.val, small⟩ allowed
  constructor
  · rw [canonicalTriplet_eq_of_coefficient_prefix _ _ (⟨3, by omega⟩ : Rank n) (3 : Rank 2) rfl
      (prefix_eq order i q small 3 (by omega) (by omega))]
    exact certificate.1
  · intro odd
    rw [canonicalTriplet_eq_of_coefficient_prefix _ _ (⟨4, by omega⟩ : Rank n) (4 : Rank 2) rfl
      (prefix_eq order i q small 4 (by omega) (by intro; exact odd))]
    exact certificate.2 odd

end Mahjong.VirtualHand.AlternatingWait
