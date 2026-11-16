/-
Copyright (c) 2026 Luna Luteus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luna Luteus
-/
module

public import Ninegates

/-! Proofs of the fixed structural challenge statements. -/

@[expose] public section

namespace ComparatorChallenges

open Mahjong Mahjong.VirtualHand

theorem virtual_criterion (n : ℕ) (c : VirtualHand n) :
    VirtuallyMeldable c ↔ (size c : ZMod 3) = 0 ∧ (rankSum c : ZMod 3) = 0 :=
  virtuallyMeldable_iff_size_rankSum c

theorem eight_family (n : ℕ) (order : 2 ≤ n) (c : VirtualHand n) :
    IsFullWait (n + 1) c ↔ Standard.EightFamily c :=
  isFullWait_iff_eightFamily order

theorem live_uniqueness (n : ℕ) (order : 2 ≤ n) (c : VirtualHand n) :
    IsLiveFullWait 4 (n + 1) c ↔ c = Standard.A n :=
  isLiveFullWait_iff_eq_A order

theorem order_one (c : VirtualHand 1) :
    IsFullWait 2 c ↔ Standard.OrderOneFamily c :=
  orderOne_isFullWait_iff_isOrderOneFamily

theorem minimal_eight_family (n : ℕ) (order : 2 ≤ n) (c : VirtualHand n) :
    IsMinimalFullWait (n + 1) c ↔ Standard.EightFamily c :=
  isMinimalFullWait_iff_eightFamily order

theorem minimal_order_one (m : ℕ) (c : VirtualHand 1) :
    IsMinimalFullWait m c ↔ m = 2 ∧ Standard.OrderOneFamily c :=
  orderOne_isMinimalFullWait_iff

theorem maximal_minimal_wait (n : ℕ) (positive : 0 < n) :
    ∃ M : ℕ, (∃ c : VirtualHand n, IsMinimalFullWait M c) ∧
      (∀ (m : ℕ) (c : VirtualHand n), IsMinimalFullWait m c → m ≤ M) ∧
        2 * n ≤ M ∧ M < 8 * n :=
  by
    obtain ⟨M, attained, maximal, bounds⟩ := exists_maximal_minimal_meldCount positive
    exact ⟨M, attained, fun _ _ h ↦ maximal h, bounds⟩

theorem alternating_even (a : ℕ) :
    IsFullWait (9 * a + 6) (AlternatingWait.even a) :=
  AlternatingWait.even_full a

theorem alternating_odd (a : ℕ) :
    IsFullWait (9 * a + 10) (AlternatingWait.odd a) :=
  AlternatingWait.odd_full a

theorem alternating_even_minimal (a : ℕ) :
    IsMinimalFullWait (9 * a + 6) (AlternatingWait.even a) :=
  AlternatingWait.even_minimal a

theorem alternating_odd_minimal (a : ℕ) :
    IsMinimalFullWait (9 * a + 10) (AlternatingWait.odd a) :=
  AlternatingWait.odd_minimal a

theorem maximal_minimal_wait_strong (n : ℕ) (positive : 0 < n) :
    ∃ M : ℕ, (∃ c : VirtualHand n, IsMinimalFullWait M c) ∧
      (∀ (m : ℕ) (c : VirtualHand n), IsMinimalFullWait m c → m ≤ M) ∧
        max (2 * n) (9 * n / 2 - 3) ≤ M ∧ M < 8 * n :=
  ⟨maxMinimalMeldCount n, exists_minimal_at_max positive, fun _ _ h ↦ h.le_max,
    maxMinimalMeldCount_strong_bounds positive⟩

theorem standard_cardinalities (n : ℕ) (order : 2 ≤ n) :
    Nat.card {c : VirtualHand n // IsFullWait (n + 1) c} = 8 ∧
      Nat.card {c : VirtualHand n // IsMinimalFullWait (n + 1) c} = 8 ∧
        Nat.card {c : VirtualHand n // IsLiveFullWait 4 (n + 1) c} = 1 :=
  ⟨fullWait_card_eight order, minimalFullWait_card_eight order, liveFullWait_card_one order⟩

theorem order_one_cardinalities :
    Nat.card {c : VirtualHand 1 // IsFullWait 2 c} = 6 ∧
      Nat.card {c : VirtualHand 1 // IsLiveFullWait 4 2 c} = 6 ∧
        Nat.card {c : VirtualHand 1 // ∃ m, IsMinimalFullWait m c} = 6 ∧
          ∀ m : ℕ, Nat.card {c : VirtualHand 1 // IsMinimalFullWait m c} =
            if m = 2 then 6 else 0 :=
  ⟨fullWait_card_six, orderOne_liveFullWait_card, orderOne_allMinimalFullWait_card,
    orderOne_minimalFullWait_card⟩

theorem below_order_cardinalities (n m : ℕ) (bound : m ≤ n) :
    Nat.card {c : VirtualHand n // IsFullWait m c} = 0 ∧
      Nat.card {c : VirtualHand n // IsMinimalFullWait m c} = 0 :=
  ⟨fullWait_card_zero bound, minimalFullWait_card_zero bound⟩

end ComparatorChallenges
