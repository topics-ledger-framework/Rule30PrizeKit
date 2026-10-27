module

public import Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFourComplete
public import Ruliology.CellularAutomata.Rule30Certificates.ZeroBoundaryStripeCycles4
public import Ruliology.CellularAutomata.Rule30Certificates.ZeroBoundaryStripeCycles5
public import Ruliology.CellularAutomata.Rule30Certificates.StripeTail97Completion

/-!
# Stripe prefixes with six and seven tail cells: mortality and `(97, 0)` completion
-/

@[expose] public section

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Ruliology.CellularAutomata
namespace Rule30ZeroBoundaryStripeSixSeven

open Rule30ZeroBoundary
open Rule30ZeroBoundaryStripe
open Rule30ZeroBoundaryStripeFront
open Rule30ZeroBoundaryStripeFront.StripeCycles0
open Rule30ZeroBoundaryStripeFront.StripeCycles1
open Rule30ZeroBoundaryStripeFront.StripeCycles2
open Rule30ZeroBoundaryStripeFront.StripeCycles3
open Rule30ZeroBoundaryStripeFront.StripeCycles4
open Rule30ZeroBoundaryStripeFront.StripeCycles5
open Rule30ZeroBoundaryStripeFourComplete
open Rule30ZeroBoundaryStripeFrontLift
open Rule30Tail97Completion

def tail6 (v i : Nat) : Bool := if i < 6 then v.testBit i else false

def row6 (m v k : Nat) : Bool :=
  if k ≤ m then stripe k else tail6 v (k - m - 1)

def dev6 (q δ v : Nat) : Bool :=
  (List.range δ).all (fun j => j == 0 || tail6 v (j - 1) == stripe (q + j)) &&
    tail6 v (δ - 1) != stripe (q + δ)

theorem family6_of_class (m q δ K S H lam v : Nat) (hq : m % 2 = q) (hδ1 : 1 ≤ δ) (hδ8 : δ ≤ 8)
    (hSK : S < K) (hSH : S ≤ H) (hdev : dev6 q δ v = true)
    (h : (q + δ) % 2 = 1 ∨
      Cycle K S (pk (fun i => tail6 v (δ - 1 + i)) K) ((q + δ) % 2) lam) :
    ∃ d, 1 ≤ d ∧ d ≤ m + 8 ∧
      (∀ k, 1 ≤ k → k < d → row6 m v k = stripe k) ∧
      row6 m v d ≠ stripe d ∧
      ∃ t, t ≤ d - 1 + H ∧ t % 2 = 0 ∧ zrow (row6 m v) t 1 = false := by
  simp only [dev6, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    beq_iff_eq, bne_iff_ne, ne_eq] at hdev
  obtain ⟨hall, hne⟩ := hdev
  have hag : ∀ k, 1 ≤ k → k < m + δ → row6 m v k = stripe k := by
    intro k hk1 hk2
    unfold row6
    by_cases hkm : k ≤ m
    · rw [ite_eq_left hkm]
    · rw [ite_eq_right hkm]
      obtain ⟨j, rfl⟩ : ∃ j, k = m + j := ⟨k - m, by omega⟩
      rw [stripe_add_mod m q j hq, show m + j - m - 1 = j - 1 by omega]
      rcases hall j (by omega) with hj | hj
      · omega
      · exact hj
  have hne' : row6 m v (m + δ) ≠ stripe (m + δ) := by
    unfold row6
    rw [ite_eq_right (by omega), show m + δ - m - 1 = δ - 1 by omega,
      stripe_add_mod m q δ hq]
    exact hne
  refine ⟨m + δ, by omega, by omega, hag, hne', ?_⟩
  rcases h with hodd | hcyc
  · exact ⟨m + δ - 1, by omega, by omega,
      first_defect_hits (row6 m v) (m + δ) (by omega) hag hne'⟩
  · have hw : pk (fun i => row6 m v (m + δ + i)) K =
        pk (fun i => tail6 v (δ - 1 + i)) K :=
      pk_congr _ _ _ fun i _ => by
        unfold row6
        rw [ite_eq_right (by omega), show m + δ + i - m - 1 = δ - 1 + i by omega]
    have hp : (m + δ) % 2 = (q + δ) % 2 := by omega
    rw [← hw, ← hp] at hcyc
    obtain ⟨s, hs, he, hz⟩ := front_sound (row6 m v) (m + δ) K S lam
      (by omega) hag (by omega) hcyc
    exact ⟨m + δ - 1 + s, by omega, he, hz⟩

private theorem range16_0 (v : Nat) (h1 : 0 ≤ v) (h2 : v < 16) :
    v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 ∨ v = 5 ∨ v = 6 ∨ v = 7 ∨ v = 8 ∨ v = 9 ∨ v = 10 ∨ v = 11 ∨ v = 12 ∨ v = 13 ∨ v = 14 ∨ v = 15 := by omega

private theorem range16_16 (v : Nat) (h1 : 16 ≤ v) (h2 : v < 32) :
    v = 16 ∨ v = 17 ∨ v = 18 ∨ v = 19 ∨ v = 20 ∨ v = 21 ∨ v = 22 ∨ v = 23 ∨ v = 24 ∨ v = 25 ∨ v = 26 ∨ v = 27 ∨ v = 28 ∨ v = 29 ∨ v = 30 ∨ v = 31 := by omega

private theorem range16_32 (v : Nat) (h1 : 32 ≤ v) (h2 : v < 48) :
    v = 32 ∨ v = 33 ∨ v = 34 ∨ v = 35 ∨ v = 36 ∨ v = 37 ∨ v = 38 ∨ v = 39 ∨ v = 40 ∨ v = 41 ∨ v = 42 ∨ v = 43 ∨ v = 44 ∨ v = 45 ∨ v = 46 ∨ v = 47 := by omega

private theorem range16_48 (v : Nat) (h1 : 48 ≤ v) (h2 : v < 64) :
    v = 48 ∨ v = 49 ∨ v = 50 ∨ v = 51 ∨ v = 52 ∨ v = 53 ∨ v = 54 ∨ v = 55 ∨ v = 56 ∨ v = 57 ∨ v = 58 ∨ v = 59 ∨ v = 60 ∨ v = 61 ∨ v = 62 ∨ v = 63 := by omega

private theorem range16_64 (v : Nat) (h1 : 64 ≤ v) (h2 : v < 80) :
    v = 64 ∨ v = 65 ∨ v = 66 ∨ v = 67 ∨ v = 68 ∨ v = 69 ∨ v = 70 ∨ v = 71 ∨ v = 72 ∨ v = 73 ∨ v = 74 ∨ v = 75 ∨ v = 76 ∨ v = 77 ∨ v = 78 ∨ v = 79 := by omega

private theorem range16_80 (v : Nat) (h1 : 80 ≤ v) (h2 : v < 96) :
    v = 80 ∨ v = 81 ∨ v = 82 ∨ v = 83 ∨ v = 84 ∨ v = 85 ∨ v = 86 ∨ v = 87 ∨ v = 88 ∨ v = 89 ∨ v = 90 ∨ v = 91 ∨ v = 92 ∨ v = 93 ∨ v = 94 ∨ v = 95 := by omega

private theorem range16_96 (v : Nat) (h1 : 96 ≤ v) (h2 : v < 112) :
    v = 96 ∨ v = 97 ∨ v = 98 ∨ v = 99 ∨ v = 100 ∨ v = 101 ∨ v = 102 ∨ v = 103 ∨ v = 104 ∨ v = 105 ∨ v = 106 ∨ v = 107 ∨ v = 108 ∨ v = 109 ∨ v = 110 ∨ v = 111 := by omega

private theorem range16_112 (v : Nat) (h1 : 112 ≤ v) (h2 : v < 128) :
    v = 112 ∨ v = 113 ∨ v = 114 ∨ v = 115 ∨ v = 116 ∨ v = 117 ∨ v = 118 ∨ v = 119 ∨ v = 120 ∨ v = 121 ∨ v = 122 ∨ v = 123 ∨ v = 124 ∨ v = 125 ∨ v = 126 ∨ v = 127 := by omega

private theorem stripe_six_q0_b0 (m v : Nat) (hq : m % 2 = 0) (h1 : 0 ≤ v) (h2 : v < 16)
    (hv : (v ≠ 13 ∨ m % 2 = 0) ∧ (v ≠ 27 ∨ m % 2 = 1) ∧ (v ≠ 54 ∨ m % 2 = 0)) :
    ∃ d, 1 ≤ d ∧ d ≤ m + 8 ∧ (∀ k, 1 ≤ k → k < d → row6 m v k = stripe k) ∧
      row6 m v d ≠ stripe d ∧ ∃ t, t ≤ d - 1 + 31 ∧ t % 2 = 0 ∧ zrow (row6 m v) t 1 = false := by
  rcases range16_0 v h1 h2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact family6_of_class m 0 1 8 7 31 0 0 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family6_of_class m 0 3 8 7 31 0 1 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family6_of_class m 0 1 8 7 31 0 2 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family6_of_class m 0 2 32 31 31 4096 3 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc_1_0))
  · exact family6_of_class m 0 1 8 7 31 0 4 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family6_of_class m 0 5 8 7 31 0 5 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family6_of_class m 0 1 8 7 31 0 6 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family6_of_class m 0 2 32 31 31 16384 7 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc_3_0))
  · exact family6_of_class m 0 1 8 7 31 0 8 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family6_of_class m 0 3 8 7 31 0 9 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family6_of_class m 0 1 8 7 31 0 10 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family6_of_class m 0 2 32 31 31 65536 11 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc_5_0))
  · exact family6_of_class m 0 1 8 7 31 0 12 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family6_of_class m 0 4 32 31 31 4096 13 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc_1_0))
  · exact family6_of_class m 0 1 8 7 31 0 14 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family6_of_class m 0 2 32 31 31 16384 15 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc_7_0))

private theorem stripe_six_q0_b1 (m v : Nat) (hq : m % 2 = 0) (h1 : 16 ≤ v) (h2 : v < 32)
    (hv : (v ≠ 13 ∨ m % 2 = 0) ∧ (v ≠ 27 ∨ m % 2 = 1) ∧ (v ≠ 54 ∨ m % 2 = 0)) :
    ∃ d, 1 ≤ d ∧ d ≤ m + 8 ∧ (∀ k, 1 ≤ k → k < d → row6 m v k = stripe k) ∧
      row6 m v d ≠ stripe d ∧ ∃ t, t ≤ d - 1 + 31 ∧ t % 2 = 0 ∧ zrow (row6 m v) t 1 = false := by
  rcases range16_16 v h1 h2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact family6_of_class m 0 1 8 7 31 0 16 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family6_of_class m 0 3 8 7 31 0 17 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family6_of_class m 0 1 8 7 31 0 18 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family6_of_class m 0 2 32 31 31 4096 19 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc4_9))
  · exact family6_of_class m 0 1 8 7 31 0 20 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family6_of_class m 0 7 8 7 31 0 21 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family6_of_class m 0 1 8 7 31 0 22 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family6_of_class m 0 2 32 31 31 65536 23 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc4_11))
  · exact family6_of_class m 0 1 8 7 31 0 24 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family6_of_class m 0 3 8 7 31 0 25 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family6_of_class m 0 1 8 7 31 0 26 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · omega
  · exact family6_of_class m 0 1 8 7 31 0 28 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family6_of_class m 0 4 32 31 31 16384 29 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc_3_0))
  · exact family6_of_class m 0 1 8 7 31 0 30 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family6_of_class m 0 2 32 31 31 16384 31 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc4_15))

private theorem stripe_six_q0_b2 (m v : Nat) (hq : m % 2 = 0) (h1 : 32 ≤ v) (h2 : v < 48)
    (hv : (v ≠ 13 ∨ m % 2 = 0) ∧ (v ≠ 27 ∨ m % 2 = 1) ∧ (v ≠ 54 ∨ m % 2 = 0)) :
    ∃ d, 1 ≤ d ∧ d ≤ m + 8 ∧ (∀ k, 1 ≤ k → k < d → row6 m v k = stripe k) ∧
      row6 m v d ≠ stripe d ∧ ∃ t, t ≤ d - 1 + 31 ∧ t % 2 = 0 ∧ zrow (row6 m v) t 1 = false := by
  rcases range16_32 v h1 h2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact family6_of_class m 0 1 8 7 31 0 32 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family6_of_class m 0 3 8 7 31 0 33 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family6_of_class m 0 1 8 7 31 0 34 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family6_of_class m 0 2 32 31 31 16384 35 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc5_17))
  · exact family6_of_class m 0 1 8 7 31 0 36 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family6_of_class m 0 5 8 7 31 0 37 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family6_of_class m 0 1 8 7 31 0 38 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family6_of_class m 0 2 32 31 31 65536 39 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc5_19))
  · exact family6_of_class m 0 1 8 7 31 0 40 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family6_of_class m 0 3 8 7 31 0 41 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family6_of_class m 0 1 8 7 31 0 42 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family6_of_class m 0 2 32 31 31 32768 43 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc5_21))
  · exact family6_of_class m 0 1 8 7 31 0 44 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family6_of_class m 0 4 32 31 31 65536 45 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc_5_0))
  · exact family6_of_class m 0 1 8 7 31 0 46 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family6_of_class m 0 2 32 31 31 16384 47 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc5_23))

private theorem stripe_six_q0_b3 (m v : Nat) (hq : m % 2 = 0) (h1 : 48 ≤ v) (h2 : v < 64)
    (hv : (v ≠ 13 ∨ m % 2 = 0) ∧ (v ≠ 27 ∨ m % 2 = 1) ∧ (v ≠ 54 ∨ m % 2 = 0)) :
    ∃ d, 1 ≤ d ∧ d ≤ m + 8 ∧ (∀ k, 1 ≤ k → k < d → row6 m v k = stripe k) ∧
      row6 m v d ≠ stripe d ∧ ∃ t, t ≤ d - 1 + 31 ∧ t % 2 = 0 ∧ zrow (row6 m v) t 1 = false := by
  rcases range16_48 v h1 h2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact family6_of_class m 0 1 8 7 31 0 48 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family6_of_class m 0 3 8 7 31 0 49 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family6_of_class m 0 1 8 7 31 0 50 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family6_of_class m 0 2 32 31 31 16384 51 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc5_25))
  · exact family6_of_class m 0 1 8 7 31 0 52 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family6_of_class m 0 6 32 31 31 4096 53 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc_1_0))
  · exact family6_of_class m 0 1 8 7 31 0 54 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family6_of_class m 0 2 32 31 31 4096 55 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc5_27))
  · exact family6_of_class m 0 1 8 7 31 0 56 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family6_of_class m 0 3 8 7 31 0 57 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family6_of_class m 0 1 8 7 31 0 58 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family6_of_class m 0 2 32 31 31 65536 59 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc5_29))
  · exact family6_of_class m 0 1 8 7 31 0 60 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family6_of_class m 0 4 32 31 31 16384 61 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc_7_0))
  · exact family6_of_class m 0 1 8 7 31 0 62 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family6_of_class m 0 2 32 31 31 65536 63 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc5_31))

private theorem stripe_six_q1_b0 (m v : Nat) (hq : m % 2 = 1) (h1 : 0 ≤ v) (h2 : v < 16)
    (hv : (v ≠ 13 ∨ m % 2 = 0) ∧ (v ≠ 27 ∨ m % 2 = 1) ∧ (v ≠ 54 ∨ m % 2 = 0)) :
    ∃ d, 1 ≤ d ∧ d ≤ m + 8 ∧ (∀ k, 1 ≤ k → k < d → row6 m v k = stripe k) ∧
      row6 m v d ≠ stripe d ∧ ∃ t, t ≤ d - 1 + 31 ∧ t % 2 = 0 ∧ zrow (row6 m v) t 1 = false := by
  rcases range16_0 v h1 h2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact family6_of_class m 1 2 8 7 31 0 0 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family6_of_class m 1 1 32 31 31 4096 1 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc_1_0))
  · exact family6_of_class m 1 4 8 7 31 0 2 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family6_of_class m 1 1 32 31 31 16384 3 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc_3_0))
  · exact family6_of_class m 1 2 8 7 31 0 4 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family6_of_class m 1 1 32 31 31 65536 5 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc_5_0))
  · exact family6_of_class m 1 3 32 31 31 4096 6 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc_1_0))
  · exact family6_of_class m 1 1 32 31 31 16384 7 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc_7_0))
  · exact family6_of_class m 1 2 8 7 31 0 8 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family6_of_class m 1 1 32 31 31 4096 9 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc4_9))
  · exact family6_of_class m 1 6 8 7 31 0 10 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family6_of_class m 1 1 32 31 31 65536 11 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc4_11))
  · exact family6_of_class m 1 2 8 7 31 0 12 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · omega
  · exact family6_of_class m 1 3 32 31 31 16384 14 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc_3_0))
  · exact family6_of_class m 1 1 32 31 31 16384 15 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc4_15))

private theorem stripe_six_q1_b1 (m v : Nat) (hq : m % 2 = 1) (h1 : 16 ≤ v) (h2 : v < 32)
    (hv : (v ≠ 13 ∨ m % 2 = 0) ∧ (v ≠ 27 ∨ m % 2 = 1) ∧ (v ≠ 54 ∨ m % 2 = 0)) :
    ∃ d, 1 ≤ d ∧ d ≤ m + 8 ∧ (∀ k, 1 ≤ k → k < d → row6 m v k = stripe k) ∧
      row6 m v d ≠ stripe d ∧ ∃ t, t ≤ d - 1 + 31 ∧ t % 2 = 0 ∧ zrow (row6 m v) t 1 = false := by
  rcases range16_16 v h1 h2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact family6_of_class m 1 2 8 7 31 0 16 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family6_of_class m 1 1 32 31 31 16384 17 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc5_17))
  · exact family6_of_class m 1 4 8 7 31 0 18 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family6_of_class m 1 1 32 31 31 65536 19 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc5_19))
  · exact family6_of_class m 1 2 8 7 31 0 20 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family6_of_class m 1 1 32 31 31 32768 21 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc5_21))
  · exact family6_of_class m 1 3 32 31 31 65536 22 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc_5_0))
  · exact family6_of_class m 1 1 32 31 31 16384 23 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc5_23))
  · exact family6_of_class m 1 2 8 7 31 0 24 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family6_of_class m 1 1 32 31 31 16384 25 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc5_25))
  · exact family6_of_class m 1 5 32 31 31 4096 26 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc_1_0))
  · exact family6_of_class m 1 1 32 31 31 4096 27 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc5_27))
  · exact family6_of_class m 1 2 8 7 31 0 28 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family6_of_class m 1 1 32 31 31 65536 29 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc5_29))
  · exact family6_of_class m 1 3 32 31 31 16384 30 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc_7_0))
  · exact family6_of_class m 1 1 32 31 31 65536 31 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc5_31))

private theorem stripe_six_q1_b2 (m v : Nat) (hq : m % 2 = 1) (h1 : 32 ≤ v) (h2 : v < 48)
    (hv : (v ≠ 13 ∨ m % 2 = 0) ∧ (v ≠ 27 ∨ m % 2 = 1) ∧ (v ≠ 54 ∨ m % 2 = 0)) :
    ∃ d, 1 ≤ d ∧ d ≤ m + 8 ∧ (∀ k, 1 ≤ k → k < d → row6 m v k = stripe k) ∧
      row6 m v d ≠ stripe d ∧ ∃ t, t ≤ d - 1 + 31 ∧ t % 2 = 0 ∧ zrow (row6 m v) t 1 = false := by
  rcases range16_32 v h1 h2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact family6_of_class m 1 2 8 7 31 0 32 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family6_of_class m 1 1 16 15 31 256 33 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc6_33))
  · exact family6_of_class m 1 4 8 7 31 0 34 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family6_of_class m 1 1 20 19 31 512 35 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc6_35))
  · exact family6_of_class m 1 2 8 7 31 0 36 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family6_of_class m 1 1 8 7 31 32 37 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc6_37))
  · exact family6_of_class m 1 3 32 31 31 4096 38 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc4_9))
  · exact family6_of_class m 1 1 28 27 31 8192 39 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc6_39))
  · exact family6_of_class m 1 2 8 7 31 0 40 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family6_of_class m 1 1 12 11 31 32 41 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc6_41))
  · exact family6_of_class m 1 8 8 7 31 0 42 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family6_of_class m 1 1 10 9 31 64 43 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc6_43))
  · exact family6_of_class m 1 2 8 7 31 0 44 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family6_of_class m 1 1 30 29 31 32768 45 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc6_45))
  · exact family6_of_class m 1 3 32 31 31 65536 46 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc4_11))
  · exact family6_of_class m 1 1 26 25 31 2048 47 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc6_47))

private theorem stripe_six_q1_b3 (m v : Nat) (hq : m % 2 = 1) (h1 : 48 ≤ v) (h2 : v < 64)
    (hv : (v ≠ 13 ∨ m % 2 = 0) ∧ (v ≠ 27 ∨ m % 2 = 1) ∧ (v ≠ 54 ∨ m % 2 = 0)) :
    ∃ d, 1 ≤ d ∧ d ≤ m + 8 ∧ (∀ k, 1 ≤ k → k < d → row6 m v k = stripe k) ∧
      row6 m v d ≠ stripe d ∧ ∃ t, t ≤ d - 1 + 31 ∧ t % 2 = 0 ∧ zrow (row6 m v) t 1 = false := by
  rcases range16_48 v h1 h2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact family6_of_class m 1 2 8 7 31 0 48 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family6_of_class m 1 1 10 9 31 64 49 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc6_49))
  · exact family6_of_class m 1 4 8 7 31 0 50 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family6_of_class m 1 1 8 7 31 32 51 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc6_51))
  · exact family6_of_class m 1 2 8 7 31 0 52 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family6_of_class m 1 1 10 9 31 32 53 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc6_53))
  · omega
  · exact family6_of_class m 1 1 24 23 31 2048 55 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc6_55))
  · exact family6_of_class m 1 2 8 7 31 0 56 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family6_of_class m 1 1 30 29 31 16384 57 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc6_57))
  · exact family6_of_class m 1 5 32 31 31 16384 58 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc_3_0))
  · exact family6_of_class m 1 1 10 9 31 64 59 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc6_59))
  · exact family6_of_class m 1 2 8 7 31 0 60 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family6_of_class m 1 1 10 9 31 64 61 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc6_61))
  · exact family6_of_class m 1 3 32 31 31 16384 62 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc4_15))
  · exact family6_of_class m 1 1 16 15 31 256 63 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc6_63))

theorem stripe_six_tail (m : Nat) (v : Fin 64)
    (hv : (v.val ≠ 13 ∨ m % 2 = 0) ∧ (v.val ≠ 27 ∨ m % 2 = 1) ∧ (v.val ≠ 54 ∨ m % 2 = 0)) :
    ∃ d, 1 ≤ d ∧ d ≤ m + 8 ∧
      (∀ k, 1 ≤ k → k < d → row6 m v.val k = stripe k) ∧
      row6 m v.val d ≠ stripe d ∧
      ∃ t, t ≤ d - 1 + 31 ∧ t % 2 = 0 ∧ zrow (row6 m v.val) t 1 = false := by
  obtain ⟨v, hv64⟩ := v
  have hsplit : (0 ≤ v ∧ v < 16) ∨ (16 ≤ v ∧ v < 32) ∨ (32 ≤ v ∧ v < 48) ∨ (48 ≤ v ∧ v < 64) := by omega
  rcases Nat.mod_two_eq_zero_or_one m with hq | hq <;>
    rcases hsplit with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact stripe_six_q0_b0 m v hq h1 h2 hv
  · exact stripe_six_q0_b1 m v hq h1 h2 hv
  · exact stripe_six_q0_b2 m v hq h1 h2 hv
  · exact stripe_six_q0_b3 m v hq h1 h2 hv
  · exact stripe_six_q1_b0 m v hq h1 h2 hv
  · exact stripe_six_q1_b1 m v hq h1 h2 hv
  · exact stripe_six_q1_b2 m v hq h1 h2 hv
  · exact stripe_six_q1_b3 m v hq h1 h2 hv

theorem row6_13_all_odd (m : Nat) (hq : m % 2 = 1) :
    ∃ d, 1 ≤ d ∧ d ≤ m + 8 ∧
      (∀ k, 1 ≤ k → k < d → row6 m 13 k = stripe k) ∧
      row6 m 13 d ≠ stripe d ∧
      ∃ t, t ≤ d - 1 + 45 ∧ t % 2 = 0 ∧ zrow (row6 m 13) t 1 = false :=
  family6_of_class m 1 1 46 45 45 2097152 13 hq (by decide) (by decide) (by decide) (by decide)
    (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cycle13_complete))

theorem row6_27_all_even (m : Nat) (hq : m % 2 = 0) :
    ∃ d, 1 ≤ d ∧ d ≤ m + 8 ∧
      (∀ k, 1 ≤ k → k < d → row6 m 27 k = stripe k) ∧
      row6 m 27 d ≠ stripe d ∧
      ∃ t, t ≤ d - 1 + 45 ∧ t % 2 = 0 ∧ zrow (row6 m 27) t 1 = false :=
  family6_of_class m 0 2 46 45 45 2097152 27 hq (by decide) (by decide) (by decide) (by decide)
    (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cycle13_complete))

theorem row6_54_all_odd (m : Nat) (hq : m % 2 = 1) :
    ∃ d, 1 ≤ d ∧ d ≤ m + 8 ∧
      (∀ k, 1 ≤ k → k < d → row6 m 54 k = stripe k) ∧
      row6 m 54 d ≠ stripe d ∧
      ∃ t, t ≤ d - 1 + 45 ∧ t % 2 = 0 ∧ zrow (row6 m 54) t 1 = false :=
  family6_of_class m 1 3 46 45 45 2097152 54 hq (by decide) (by decide) (by decide) (by decide)
    (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cycle13_complete))

theorem stripe_six_tail_complete (m : Nat) (v : Fin 64) :
    ∃ d, 1 ≤ d ∧ d ≤ m + 8 ∧
      (∀ k, 1 ≤ k → k < d → row6 m v.val k = stripe k) ∧
      row6 m v.val d ≠ stripe d ∧
      ∃ t, t ≤ d - 1 + 45 ∧ t % 2 = 0 ∧ zrow (row6 m v.val) t 1 = false := by
  by_cases h : (v.val ≠ 13 ∨ m % 2 = 0) ∧ (v.val ≠ 27 ∨ m % 2 = 1) ∧ (v.val ≠ 54 ∨ m % 2 = 0)
  · obtain ⟨d, hd, hdm, hag, hdev, t, ht, he, hz⟩ := stripe_six_tail m v h
    exact ⟨d, hd, hdm, hag, hdev, t, by omega, he, hz⟩
  · rcases (show (v.val = 13 ∧ m % 2 = 1) ∨ (v.val = 27 ∧ m % 2 = 0) ∨ (v.val = 54 ∧ m % 2 = 1) by omega)
      with ⟨hv, hq⟩ | ⟨hv, hq⟩ | ⟨hv, hq⟩
    · rw [hv]; exact row6_13_all_odd m hq
    · rw [hv]; exact row6_27_all_even m hq
    · rw [hv]; exact row6_54_all_odd m hq

def tail7 (v i : Nat) : Bool := if i < 7 then v.testBit i else false

def row7 (m v k : Nat) : Bool :=
  if k ≤ m then stripe k else tail7 v (k - m - 1)

def dev7 (q δ v : Nat) : Bool :=
  (List.range δ).all (fun j => j == 0 || tail7 v (j - 1) == stripe (q + j)) &&
    tail7 v (δ - 1) != stripe (q + δ)

theorem family7_of_class (m q δ K S H lam v : Nat) (hq : m % 2 = q) (hδ1 : 1 ≤ δ) (hδ9 : δ ≤ 9)
    (hSK : S < K) (hSH : S ≤ H) (hdev : dev7 q δ v = true)
    (h : (q + δ) % 2 = 1 ∨
      Cycle K S (pk (fun i => tail7 v (δ - 1 + i)) K) ((q + δ) % 2) lam) :
    ∃ d, 1 ≤ d ∧ d ≤ m + 9 ∧
      (∀ k, 1 ≤ k → k < d → row7 m v k = stripe k) ∧
      row7 m v d ≠ stripe d ∧
      ∃ t, t ≤ d - 1 + H ∧ t % 2 = 0 ∧ zrow (row7 m v) t 1 = false := by
  simp only [dev7, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    beq_iff_eq, bne_iff_ne, ne_eq] at hdev
  obtain ⟨hall, hne⟩ := hdev
  have hag : ∀ k, 1 ≤ k → k < m + δ → row7 m v k = stripe k := by
    intro k hk1 hk2
    unfold row7
    by_cases hkm : k ≤ m
    · rw [ite_eq_left hkm]
    · rw [ite_eq_right hkm]
      obtain ⟨j, rfl⟩ : ∃ j, k = m + j := ⟨k - m, by omega⟩
      rw [stripe_add_mod m q j hq, show m + j - m - 1 = j - 1 by omega]
      rcases hall j (by omega) with hj | hj
      · omega
      · exact hj
  have hne' : row7 m v (m + δ) ≠ stripe (m + δ) := by
    unfold row7
    rw [ite_eq_right (by omega), show m + δ - m - 1 = δ - 1 by omega,
      stripe_add_mod m q δ hq]
    exact hne
  refine ⟨m + δ, by omega, by omega, hag, hne', ?_⟩
  rcases h with hodd | hcyc
  · exact ⟨m + δ - 1, by omega, by omega,
      first_defect_hits (row7 m v) (m + δ) (by omega) hag hne'⟩
  · have hw : pk (fun i => row7 m v (m + δ + i)) K =
        pk (fun i => tail7 v (δ - 1 + i)) K :=
      pk_congr _ _ _ fun i _ => by
        unfold row7
        rw [ite_eq_right (by omega), show m + δ + i - m - 1 = δ - 1 + i by omega]
    have hp : (m + δ) % 2 = (q + δ) % 2 := by omega
    rw [← hw, ← hp] at hcyc
    obtain ⟨s, hs, he, hz⟩ := front_sound (row7 m v) (m + δ) K S lam
      (by omega) hag (by omega) hcyc
    exact ⟨m + δ - 1 + s, by omega, he, hz⟩

theorem full_jump97 (j : Nat) (hj : j < 32) :
    orb 36 8192 (Rule30Tail97Completion.embedding j, 0) =
      (Rule30Tail97Completion.embedding (Rule30Tail97Completion.nextIndex j), 0) := by
  have h := run_correct (ALL := Rule30Tail97Completion.lanes) (p := j) (K := 26)
    (s := Rule30Tail97Completion.state000)
    (Rule30Tail97Completion.lanes_bit j hj) (by decide) (by decide) (by decide) 8192
  rw [Rule30Tail97Completion.run_full, Rule30Tail97Completion.initial_word j hj,
    Rule30Tail97Completion.endpoint_word j hj] at h
  exact h

theorem prefix_jump97 (j : Nat) (hj : j < 32) :
    orb 36 6313 (Rule30Tail97Completion.embedding j, 0) =
      (Rule30Tail97Completion.prefixWord j, 1) := by
  have h := run_correct (ALL := Rule30Tail97Completion.lanes) (p := j) (K := 26)
    (s := Rule30Tail97Completion.state000)
    (Rule30Tail97Completion.lanes_bit j hj) (by decide) (by decide) (by decide) 6313
  rw [Rule30Tail97Completion.run_prefix, Rule30Tail97Completion.initial_word j hj] at h
  exact h

theorem cycle97_complete : Cycle 36 35 97 0 262144 := by
  change Cycle 36 35 (Rule30Tail97Completion.embedding 0) 0 (8192 * 32)
  apply return_map_cycle_lift (Klo := 26) (Khi := 36) (Slo := 25) (Shi := 35)
    (B := 97) (p := 0) (L := 8192) (N := 32) (u := 0) (q := 32)
    (J := Rule30Tail97Completion.nextIndex) (embed := Rule30Tail97Completion.embedding)
    (E := fun r => r = 6313)
    (by decide) (by decide) (by decide) (by decide) (fun _ _ => rfl)
    (by decide) (by decide) Rule30Tail97Completion.cyc97_period
  · intro r hr hp hne
    exact Rule30Tail97Completion.cyc97_sig r hr hp hne
  · intro v _
    exact Nat.mod_lt (v + 1) (by decide)
  · decide
  · exact full_jump97
  · decide
  · exact Rule30Tail97Completion.return_cycle
  · intro j hj e _ _ he
    subst e
    rw [Rule30Tail97Completion.iter_index j hj, prefix_jump97 j hj]
    exact Rule30Tail97Completion.rare_table_sound j hj

private theorem stripe_seven_q0_b0 (m v : Nat) (hq : m % 2 = 0) (h1 : 0 ≤ v) (h2 : v < 16)
    (hv : (v ≠ 13 ∨ m % 2 = 0) ∧ (v ≠ 27 ∨ m % 2 = 1) ∧ (v ≠ 54 ∨ m % 2 = 0) ∧ (v ≠ 109 ∨ m % 2 = 1) ∧ (v ≠ 97 ∨ m % 2 = 0)) :
    ∃ d, 1 ≤ d ∧ d ≤ m + 9 ∧ (∀ k, 1 ≤ k → k < d → row7 m v k = stripe k) ∧
      row7 m v d ≠ stripe d ∧ ∃ t, t ≤ d - 1 + 31 ∧ t % 2 = 0 ∧ zrow (row7 m v) t 1 = false := by
  rcases range16_0 v h1 h2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact family7_of_class m 0 1 8 7 31 0 0 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 0 3 8 7 31 0 1 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 0 1 8 7 31 0 2 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 0 2 32 31 31 4096 3 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc_1_0))
  · exact family7_of_class m 0 1 8 7 31 0 4 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 0 5 8 7 31 0 5 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 0 1 8 7 31 0 6 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 0 2 32 31 31 16384 7 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc_3_0))
  · exact family7_of_class m 0 1 8 7 31 0 8 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 0 3 8 7 31 0 9 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 0 1 8 7 31 0 10 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 0 2 32 31 31 65536 11 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc_5_0))
  · exact family7_of_class m 0 1 8 7 31 0 12 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 0 4 32 31 31 4096 13 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc_1_0))
  · exact family7_of_class m 0 1 8 7 31 0 14 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 0 2 32 31 31 16384 15 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc_7_0))

private theorem stripe_seven_q0_b1 (m v : Nat) (hq : m % 2 = 0) (h1 : 16 ≤ v) (h2 : v < 32)
    (hv : (v ≠ 13 ∨ m % 2 = 0) ∧ (v ≠ 27 ∨ m % 2 = 1) ∧ (v ≠ 54 ∨ m % 2 = 0) ∧ (v ≠ 109 ∨ m % 2 = 1) ∧ (v ≠ 97 ∨ m % 2 = 0)) :
    ∃ d, 1 ≤ d ∧ d ≤ m + 9 ∧ (∀ k, 1 ≤ k → k < d → row7 m v k = stripe k) ∧
      row7 m v d ≠ stripe d ∧ ∃ t, t ≤ d - 1 + 31 ∧ t % 2 = 0 ∧ zrow (row7 m v) t 1 = false := by
  rcases range16_16 v h1 h2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact family7_of_class m 0 1 8 7 31 0 16 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 0 3 8 7 31 0 17 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 0 1 8 7 31 0 18 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 0 2 32 31 31 4096 19 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc4_9))
  · exact family7_of_class m 0 1 8 7 31 0 20 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 0 7 8 7 31 0 21 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 0 1 8 7 31 0 22 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 0 2 32 31 31 65536 23 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc4_11))
  · exact family7_of_class m 0 1 8 7 31 0 24 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 0 3 8 7 31 0 25 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 0 1 8 7 31 0 26 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · omega
  · exact family7_of_class m 0 1 8 7 31 0 28 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 0 4 32 31 31 16384 29 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc_3_0))
  · exact family7_of_class m 0 1 8 7 31 0 30 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 0 2 32 31 31 16384 31 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc4_15))

private theorem stripe_seven_q0_b2 (m v : Nat) (hq : m % 2 = 0) (h1 : 32 ≤ v) (h2 : v < 48)
    (hv : (v ≠ 13 ∨ m % 2 = 0) ∧ (v ≠ 27 ∨ m % 2 = 1) ∧ (v ≠ 54 ∨ m % 2 = 0) ∧ (v ≠ 109 ∨ m % 2 = 1) ∧ (v ≠ 97 ∨ m % 2 = 0)) :
    ∃ d, 1 ≤ d ∧ d ≤ m + 9 ∧ (∀ k, 1 ≤ k → k < d → row7 m v k = stripe k) ∧
      row7 m v d ≠ stripe d ∧ ∃ t, t ≤ d - 1 + 31 ∧ t % 2 = 0 ∧ zrow (row7 m v) t 1 = false := by
  rcases range16_32 v h1 h2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact family7_of_class m 0 1 8 7 31 0 32 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 0 3 8 7 31 0 33 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 0 1 8 7 31 0 34 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 0 2 32 31 31 16384 35 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc5_17))
  · exact family7_of_class m 0 1 8 7 31 0 36 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 0 5 8 7 31 0 37 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 0 1 8 7 31 0 38 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 0 2 32 31 31 65536 39 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc5_19))
  · exact family7_of_class m 0 1 8 7 31 0 40 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 0 3 8 7 31 0 41 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 0 1 8 7 31 0 42 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 0 2 32 31 31 32768 43 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc5_21))
  · exact family7_of_class m 0 1 8 7 31 0 44 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 0 4 32 31 31 65536 45 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc_5_0))
  · exact family7_of_class m 0 1 8 7 31 0 46 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 0 2 32 31 31 16384 47 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc5_23))

private theorem stripe_seven_q0_b3 (m v : Nat) (hq : m % 2 = 0) (h1 : 48 ≤ v) (h2 : v < 64)
    (hv : (v ≠ 13 ∨ m % 2 = 0) ∧ (v ≠ 27 ∨ m % 2 = 1) ∧ (v ≠ 54 ∨ m % 2 = 0) ∧ (v ≠ 109 ∨ m % 2 = 1) ∧ (v ≠ 97 ∨ m % 2 = 0)) :
    ∃ d, 1 ≤ d ∧ d ≤ m + 9 ∧ (∀ k, 1 ≤ k → k < d → row7 m v k = stripe k) ∧
      row7 m v d ≠ stripe d ∧ ∃ t, t ≤ d - 1 + 31 ∧ t % 2 = 0 ∧ zrow (row7 m v) t 1 = false := by
  rcases range16_48 v h1 h2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact family7_of_class m 0 1 8 7 31 0 48 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 0 3 8 7 31 0 49 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 0 1 8 7 31 0 50 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 0 2 32 31 31 16384 51 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc5_25))
  · exact family7_of_class m 0 1 8 7 31 0 52 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 0 6 32 31 31 4096 53 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc_1_0))
  · exact family7_of_class m 0 1 8 7 31 0 54 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 0 2 32 31 31 4096 55 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc5_27))
  · exact family7_of_class m 0 1 8 7 31 0 56 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 0 3 8 7 31 0 57 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 0 1 8 7 31 0 58 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 0 2 32 31 31 65536 59 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc5_29))
  · exact family7_of_class m 0 1 8 7 31 0 60 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 0 4 32 31 31 16384 61 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc_7_0))
  · exact family7_of_class m 0 1 8 7 31 0 62 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 0 2 32 31 31 65536 63 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc5_31))

private theorem stripe_seven_q0_b4 (m v : Nat) (hq : m % 2 = 0) (h1 : 64 ≤ v) (h2 : v < 80)
    (hv : (v ≠ 13 ∨ m % 2 = 0) ∧ (v ≠ 27 ∨ m % 2 = 1) ∧ (v ≠ 54 ∨ m % 2 = 0) ∧ (v ≠ 109 ∨ m % 2 = 1) ∧ (v ≠ 97 ∨ m % 2 = 0)) :
    ∃ d, 1 ≤ d ∧ d ≤ m + 9 ∧ (∀ k, 1 ≤ k → k < d → row7 m v k = stripe k) ∧
      row7 m v d ≠ stripe d ∧ ∃ t, t ≤ d - 1 + 31 ∧ t % 2 = 0 ∧ zrow (row7 m v) t 1 = false := by
  rcases range16_64 v h1 h2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact family7_of_class m 0 1 8 7 31 0 64 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 0 3 8 7 31 0 65 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 0 1 8 7 31 0 66 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 0 2 16 15 31 256 67 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc6_33))
  · exact family7_of_class m 0 1 8 7 31 0 68 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 0 5 8 7 31 0 69 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 0 1 8 7 31 0 70 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 0 2 20 19 31 512 71 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc6_35))
  · exact family7_of_class m 0 1 8 7 31 0 72 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 0 3 8 7 31 0 73 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 0 1 8 7 31 0 74 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 0 2 8 7 31 32 75 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc6_37))
  · exact family7_of_class m 0 1 8 7 31 0 76 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 0 4 32 31 31 4096 77 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc4_9))
  · exact family7_of_class m 0 1 8 7 31 0 78 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 0 2 28 27 31 8192 79 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc6_39))

private theorem stripe_seven_q0_b5 (m v : Nat) (hq : m % 2 = 0) (h1 : 80 ≤ v) (h2 : v < 96)
    (hv : (v ≠ 13 ∨ m % 2 = 0) ∧ (v ≠ 27 ∨ m % 2 = 1) ∧ (v ≠ 54 ∨ m % 2 = 0) ∧ (v ≠ 109 ∨ m % 2 = 1) ∧ (v ≠ 97 ∨ m % 2 = 0)) :
    ∃ d, 1 ≤ d ∧ d ≤ m + 9 ∧ (∀ k, 1 ≤ k → k < d → row7 m v k = stripe k) ∧
      row7 m v d ≠ stripe d ∧ ∃ t, t ≤ d - 1 + 31 ∧ t % 2 = 0 ∧ zrow (row7 m v) t 1 = false := by
  rcases range16_80 v h1 h2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact family7_of_class m 0 1 8 7 31 0 80 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 0 3 8 7 31 0 81 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 0 1 8 7 31 0 82 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 0 2 12 11 31 32 83 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc6_41))
  · exact family7_of_class m 0 1 8 7 31 0 84 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 0 9 8 7 31 0 85 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 0 1 8 7 31 0 86 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 0 2 10 9 31 64 87 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc6_43))
  · exact family7_of_class m 0 1 8 7 31 0 88 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 0 3 8 7 31 0 89 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 0 1 8 7 31 0 90 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 0 2 30 29 31 32768 91 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc6_45))
  · exact family7_of_class m 0 1 8 7 31 0 92 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 0 4 32 31 31 65536 93 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc4_11))
  · exact family7_of_class m 0 1 8 7 31 0 94 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 0 2 26 25 31 2048 95 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc6_47))

private theorem stripe_seven_q0_b6 (m v : Nat) (hq : m % 2 = 0) (h1 : 96 ≤ v) (h2 : v < 112)
    (hv : (v ≠ 13 ∨ m % 2 = 0) ∧ (v ≠ 27 ∨ m % 2 = 1) ∧ (v ≠ 54 ∨ m % 2 = 0) ∧ (v ≠ 109 ∨ m % 2 = 1) ∧ (v ≠ 97 ∨ m % 2 = 0)) :
    ∃ d, 1 ≤ d ∧ d ≤ m + 9 ∧ (∀ k, 1 ≤ k → k < d → row7 m v k = stripe k) ∧
      row7 m v d ≠ stripe d ∧ ∃ t, t ≤ d - 1 + 31 ∧ t % 2 = 0 ∧ zrow (row7 m v) t 1 = false := by
  rcases range16_96 v h1 h2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact family7_of_class m 0 1 8 7 31 0 96 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 0 3 8 7 31 0 97 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 0 1 8 7 31 0 98 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 0 2 10 9 31 64 99 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc6_49))
  · exact family7_of_class m 0 1 8 7 31 0 100 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 0 5 8 7 31 0 101 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 0 1 8 7 31 0 102 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 0 2 8 7 31 32 103 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc6_51))
  · exact family7_of_class m 0 1 8 7 31 0 104 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 0 3 8 7 31 0 105 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 0 1 8 7 31 0 106 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 0 2 10 9 31 32 107 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc6_53))
  · exact family7_of_class m 0 1 8 7 31 0 108 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · omega
  · exact family7_of_class m 0 1 8 7 31 0 110 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 0 2 24 23 31 2048 111 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc6_55))

private theorem stripe_seven_q0_b7 (m v : Nat) (hq : m % 2 = 0) (h1 : 112 ≤ v) (h2 : v < 128)
    (hv : (v ≠ 13 ∨ m % 2 = 0) ∧ (v ≠ 27 ∨ m % 2 = 1) ∧ (v ≠ 54 ∨ m % 2 = 0) ∧ (v ≠ 109 ∨ m % 2 = 1) ∧ (v ≠ 97 ∨ m % 2 = 0)) :
    ∃ d, 1 ≤ d ∧ d ≤ m + 9 ∧ (∀ k, 1 ≤ k → k < d → row7 m v k = stripe k) ∧
      row7 m v d ≠ stripe d ∧ ∃ t, t ≤ d - 1 + 31 ∧ t % 2 = 0 ∧ zrow (row7 m v) t 1 = false := by
  rcases range16_112 v h1 h2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact family7_of_class m 0 1 8 7 31 0 112 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 0 3 8 7 31 0 113 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 0 1 8 7 31 0 114 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 0 2 30 29 31 16384 115 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc6_57))
  · exact family7_of_class m 0 1 8 7 31 0 116 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 0 6 32 31 31 16384 117 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc_3_0))
  · exact family7_of_class m 0 1 8 7 31 0 118 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 0 2 10 9 31 64 119 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc6_59))
  · exact family7_of_class m 0 1 8 7 31 0 120 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 0 3 8 7 31 0 121 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 0 1 8 7 31 0 122 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 0 2 10 9 31 64 123 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc6_61))
  · exact family7_of_class m 0 1 8 7 31 0 124 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 0 4 32 31 31 16384 125 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc4_15))
  · exact family7_of_class m 0 1 8 7 31 0 126 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 0 2 16 15 31 256 127 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc6_63))

private theorem stripe_seven_q1_b0 (m v : Nat) (hq : m % 2 = 1) (h1 : 0 ≤ v) (h2 : v < 16)
    (hv : (v ≠ 13 ∨ m % 2 = 0) ∧ (v ≠ 27 ∨ m % 2 = 1) ∧ (v ≠ 54 ∨ m % 2 = 0) ∧ (v ≠ 109 ∨ m % 2 = 1) ∧ (v ≠ 97 ∨ m % 2 = 0)) :
    ∃ d, 1 ≤ d ∧ d ≤ m + 9 ∧ (∀ k, 1 ≤ k → k < d → row7 m v k = stripe k) ∧
      row7 m v d ≠ stripe d ∧ ∃ t, t ≤ d - 1 + 31 ∧ t % 2 = 0 ∧ zrow (row7 m v) t 1 = false := by
  rcases range16_0 v h1 h2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact family7_of_class m 1 2 8 7 31 0 0 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 1 1 32 31 31 4096 1 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc_1_0))
  · exact family7_of_class m 1 4 8 7 31 0 2 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 1 1 32 31 31 16384 3 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc_3_0))
  · exact family7_of_class m 1 2 8 7 31 0 4 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 1 1 32 31 31 65536 5 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc_5_0))
  · exact family7_of_class m 1 3 32 31 31 4096 6 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc_1_0))
  · exact family7_of_class m 1 1 32 31 31 16384 7 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc_7_0))
  · exact family7_of_class m 1 2 8 7 31 0 8 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 1 1 32 31 31 4096 9 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc4_9))
  · exact family7_of_class m 1 6 8 7 31 0 10 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 1 1 32 31 31 65536 11 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc4_11))
  · exact family7_of_class m 1 2 8 7 31 0 12 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · omega
  · exact family7_of_class m 1 3 32 31 31 16384 14 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc_3_0))
  · exact family7_of_class m 1 1 32 31 31 16384 15 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc4_15))

private theorem stripe_seven_q1_b1 (m v : Nat) (hq : m % 2 = 1) (h1 : 16 ≤ v) (h2 : v < 32)
    (hv : (v ≠ 13 ∨ m % 2 = 0) ∧ (v ≠ 27 ∨ m % 2 = 1) ∧ (v ≠ 54 ∨ m % 2 = 0) ∧ (v ≠ 109 ∨ m % 2 = 1) ∧ (v ≠ 97 ∨ m % 2 = 0)) :
    ∃ d, 1 ≤ d ∧ d ≤ m + 9 ∧ (∀ k, 1 ≤ k → k < d → row7 m v k = stripe k) ∧
      row7 m v d ≠ stripe d ∧ ∃ t, t ≤ d - 1 + 31 ∧ t % 2 = 0 ∧ zrow (row7 m v) t 1 = false := by
  rcases range16_16 v h1 h2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact family7_of_class m 1 2 8 7 31 0 16 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 1 1 32 31 31 16384 17 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc5_17))
  · exact family7_of_class m 1 4 8 7 31 0 18 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 1 1 32 31 31 65536 19 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc5_19))
  · exact family7_of_class m 1 2 8 7 31 0 20 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 1 1 32 31 31 32768 21 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc5_21))
  · exact family7_of_class m 1 3 32 31 31 65536 22 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc_5_0))
  · exact family7_of_class m 1 1 32 31 31 16384 23 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc5_23))
  · exact family7_of_class m 1 2 8 7 31 0 24 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 1 1 32 31 31 16384 25 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc5_25))
  · exact family7_of_class m 1 5 32 31 31 4096 26 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc_1_0))
  · exact family7_of_class m 1 1 32 31 31 4096 27 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc5_27))
  · exact family7_of_class m 1 2 8 7 31 0 28 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 1 1 32 31 31 65536 29 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc5_29))
  · exact family7_of_class m 1 3 32 31 31 16384 30 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc_7_0))
  · exact family7_of_class m 1 1 32 31 31 65536 31 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc5_31))

private theorem stripe_seven_q1_b2 (m v : Nat) (hq : m % 2 = 1) (h1 : 32 ≤ v) (h2 : v < 48)
    (hv : (v ≠ 13 ∨ m % 2 = 0) ∧ (v ≠ 27 ∨ m % 2 = 1) ∧ (v ≠ 54 ∨ m % 2 = 0) ∧ (v ≠ 109 ∨ m % 2 = 1) ∧ (v ≠ 97 ∨ m % 2 = 0)) :
    ∃ d, 1 ≤ d ∧ d ≤ m + 9 ∧ (∀ k, 1 ≤ k → k < d → row7 m v k = stripe k) ∧
      row7 m v d ≠ stripe d ∧ ∃ t, t ≤ d - 1 + 31 ∧ t % 2 = 0 ∧ zrow (row7 m v) t 1 = false := by
  rcases range16_32 v h1 h2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact family7_of_class m 1 2 8 7 31 0 32 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 1 1 16 15 31 256 33 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc6_33))
  · exact family7_of_class m 1 4 8 7 31 0 34 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 1 1 20 19 31 512 35 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc6_35))
  · exact family7_of_class m 1 2 8 7 31 0 36 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 1 1 8 7 31 32 37 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc6_37))
  · exact family7_of_class m 1 3 32 31 31 4096 38 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc4_9))
  · exact family7_of_class m 1 1 28 27 31 8192 39 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc6_39))
  · exact family7_of_class m 1 2 8 7 31 0 40 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 1 1 12 11 31 32 41 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc6_41))
  · exact family7_of_class m 1 8 8 7 31 0 42 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 1 1 10 9 31 64 43 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc6_43))
  · exact family7_of_class m 1 2 8 7 31 0 44 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 1 1 30 29 31 32768 45 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc6_45))
  · exact family7_of_class m 1 3 32 31 31 65536 46 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc4_11))
  · exact family7_of_class m 1 1 26 25 31 2048 47 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc6_47))

private theorem stripe_seven_q1_b3 (m v : Nat) (hq : m % 2 = 1) (h1 : 48 ≤ v) (h2 : v < 64)
    (hv : (v ≠ 13 ∨ m % 2 = 0) ∧ (v ≠ 27 ∨ m % 2 = 1) ∧ (v ≠ 54 ∨ m % 2 = 0) ∧ (v ≠ 109 ∨ m % 2 = 1) ∧ (v ≠ 97 ∨ m % 2 = 0)) :
    ∃ d, 1 ≤ d ∧ d ≤ m + 9 ∧ (∀ k, 1 ≤ k → k < d → row7 m v k = stripe k) ∧
      row7 m v d ≠ stripe d ∧ ∃ t, t ≤ d - 1 + 31 ∧ t % 2 = 0 ∧ zrow (row7 m v) t 1 = false := by
  rcases range16_48 v h1 h2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact family7_of_class m 1 2 8 7 31 0 48 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 1 1 10 9 31 64 49 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc6_49))
  · exact family7_of_class m 1 4 8 7 31 0 50 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 1 1 8 7 31 32 51 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc6_51))
  · exact family7_of_class m 1 2 8 7 31 0 52 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 1 1 10 9 31 32 53 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc6_53))
  · omega
  · exact family7_of_class m 1 1 24 23 31 2048 55 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc6_55))
  · exact family7_of_class m 1 2 8 7 31 0 56 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 1 1 30 29 31 16384 57 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc6_57))
  · exact family7_of_class m 1 5 32 31 31 16384 58 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc_3_0))
  · exact family7_of_class m 1 1 10 9 31 64 59 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc6_59))
  · exact family7_of_class m 1 2 8 7 31 0 60 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 1 1 10 9 31 64 61 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc6_61))
  · exact family7_of_class m 1 3 32 31 31 16384 62 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc4_15))
  · exact family7_of_class m 1 1 16 15 31 256 63 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc6_63))

private theorem stripe_seven_q1_b4 (m v : Nat) (hq : m % 2 = 1) (h1 : 64 ≤ v) (h2 : v < 80)
    (hv : (v ≠ 13 ∨ m % 2 = 0) ∧ (v ≠ 27 ∨ m % 2 = 1) ∧ (v ≠ 54 ∨ m % 2 = 0) ∧ (v ≠ 109 ∨ m % 2 = 1) ∧ (v ≠ 97 ∨ m % 2 = 0)) :
    ∃ d, 1 ≤ d ∧ d ≤ m + 9 ∧ (∀ k, 1 ≤ k → k < d → row7 m v k = stripe k) ∧
      row7 m v d ≠ stripe d ∧ ∃ t, t ≤ d - 1 + 31 ∧ t % 2 = 0 ∧ zrow (row7 m v) t 1 = false := by
  rcases range16_64 v h1 h2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact family7_of_class m 1 2 8 7 31 0 64 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 1 1 10 9 31 64 65 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc7_65))
  · exact family7_of_class m 1 4 8 7 31 0 66 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 1 1 8 7 31 32 67 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc7_67))
  · exact family7_of_class m 1 2 8 7 31 0 68 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 1 1 18 17 31 512 69 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc7_69))
  · exact family7_of_class m 1 3 32 31 31 16384 70 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc5_17))
  · exact family7_of_class m 1 1 10 9 31 32 71 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc7_71))
  · exact family7_of_class m 1 2 8 7 31 0 72 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 1 1 18 17 31 512 73 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc7_73))
  · exact family7_of_class m 1 6 8 7 31 0 74 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 1 1 10 9 31 64 75 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc7_75))
  · exact family7_of_class m 1 2 8 7 31 0 76 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 1 1 24 23 31 4096 77 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc7_77))
  · exact family7_of_class m 1 3 32 31 31 65536 78 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc5_19))
  · exact family7_of_class m 1 1 16 15 31 512 79 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc7_79))

private theorem stripe_seven_q1_b5 (m v : Nat) (hq : m % 2 = 1) (h1 : 80 ≤ v) (h2 : v < 96)
    (hv : (v ≠ 13 ∨ m % 2 = 0) ∧ (v ≠ 27 ∨ m % 2 = 1) ∧ (v ≠ 54 ∨ m % 2 = 0) ∧ (v ≠ 109 ∨ m % 2 = 1) ∧ (v ≠ 97 ∨ m % 2 = 0)) :
    ∃ d, 1 ≤ d ∧ d ≤ m + 9 ∧ (∀ k, 1 ≤ k → k < d → row7 m v k = stripe k) ∧
      row7 m v d ≠ stripe d ∧ ∃ t, t ≤ d - 1 + 31 ∧ t % 2 = 0 ∧ zrow (row7 m v) t 1 = false := by
  rcases range16_80 v h1 h2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact family7_of_class m 1 2 8 7 31 0 80 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 1 1 26 25 31 8192 81 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc7_81))
  · exact family7_of_class m 1 4 8 7 31 0 82 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 1 1 20 19 31 2048 83 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc7_83))
  · exact family7_of_class m 1 2 8 7 31 0 84 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 1 1 22 21 31 2048 85 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc7_85))
  · exact family7_of_class m 1 3 32 31 31 32768 86 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc5_21))
  · exact family7_of_class m 1 1 18 17 31 1024 87 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc7_87))
  · exact family7_of_class m 1 2 8 7 31 0 88 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 1 1 22 21 31 4096 89 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc7_89))
  · exact family7_of_class m 1 5 32 31 31 65536 90 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc_5_0))
  · exact family7_of_class m 1 1 22 21 31 4096 91 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc7_91))
  · exact family7_of_class m 1 2 8 7 31 0 92 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 1 1 10 9 31 64 93 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc7_93))
  · exact family7_of_class m 1 3 32 31 31 16384 94 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc5_23))
  · exact family7_of_class m 1 1 10 9 31 64 95 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc7_95))

private theorem stripe_seven_q1_b6 (m v : Nat) (hq : m % 2 = 1) (h1 : 96 ≤ v) (h2 : v < 112)
    (hv : (v ≠ 13 ∨ m % 2 = 0) ∧ (v ≠ 27 ∨ m % 2 = 1) ∧ (v ≠ 54 ∨ m % 2 = 0) ∧ (v ≠ 109 ∨ m % 2 = 1) ∧ (v ≠ 97 ∨ m % 2 = 0)) :
    ∃ d, 1 ≤ d ∧ d ≤ m + 9 ∧ (∀ k, 1 ≤ k → k < d → row7 m v k = stripe k) ∧
      row7 m v d ≠ stripe d ∧ ∃ t, t ≤ d - 1 + 31 ∧ t % 2 = 0 ∧ zrow (row7 m v) t 1 = false := by
  rcases range16_96 v h1 h2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact family7_of_class m 1 2 8 7 31 0 96 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · omega
  · exact family7_of_class m 1 4 8 7 31 0 98 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 1 1 20 19 31 2048 99 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc7_99))
  · exact family7_of_class m 1 2 8 7 31 0 100 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 1 1 30 29 31 16384 101 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc7_101))
  · exact family7_of_class m 1 3 32 31 31 16384 102 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc5_25))
  · exact family7_of_class m 1 1 10 9 31 32 103 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc7_103))
  · exact family7_of_class m 1 2 8 7 31 0 104 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 1 1 8 7 31 32 105 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc7_105))
  · exact family7_of_class m 1 7 32 31 31 4096 106 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc_1_0))
  · exact family7_of_class m 1 1 10 9 31 64 107 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc7_107))
  · exact family7_of_class m 1 2 8 7 31 0 108 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 1 1 10 9 31 64 109 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc7_109))
  · exact family7_of_class m 1 3 32 31 31 4096 110 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc5_27))
  · exact family7_of_class m 1 1 24 23 31 1024 111 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc7_111))

private theorem stripe_seven_q1_b7 (m v : Nat) (hq : m % 2 = 1) (h1 : 112 ≤ v) (h2 : v < 128)
    (hv : (v ≠ 13 ∨ m % 2 = 0) ∧ (v ≠ 27 ∨ m % 2 = 1) ∧ (v ≠ 54 ∨ m % 2 = 0) ∧ (v ≠ 109 ∨ m % 2 = 1) ∧ (v ≠ 97 ∨ m % 2 = 0)) :
    ∃ d, 1 ≤ d ∧ d ≤ m + 9 ∧ (∀ k, 1 ≤ k → k < d → row7 m v k = stripe k) ∧
      row7 m v d ≠ stripe d ∧ ∃ t, t ≤ d - 1 + 31 ∧ t % 2 = 0 ∧ zrow (row7 m v) t 1 = false := by
  rcases range16_112 v h1 h2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact family7_of_class m 1 2 8 7 31 0 112 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 1 1 18 17 31 512 113 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc7_113))
  · exact family7_of_class m 1 4 8 7 31 0 114 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 1 1 24 23 31 2048 115 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc7_115))
  · exact family7_of_class m 1 2 8 7 31 0 116 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 1 1 8 7 31 32 117 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc7_117))
  · exact family7_of_class m 1 3 32 31 31 65536 118 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc5_29))
  · exact family7_of_class m 1 1 10 9 31 32 119 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc7_119))
  · exact family7_of_class m 1 2 8 7 31 0 120 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 1 1 14 13 31 128 121 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc7_121))
  · exact family7_of_class m 1 5 32 31 31 16384 122 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc_7_0))
  · exact family7_of_class m 1 1 10 9 31 64 123 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc7_123))
  · exact family7_of_class m 1 2 8 7 31 0 124 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inl (by decide))
  · exact family7_of_class m 1 1 10 9 31 64 125 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc7_125))
  · exact family7_of_class m 1 3 32 31 31 65536 126 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc5_31))
  · exact family7_of_class m 1 1 22 21 31 1024 127 hq (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cyc7_127))

theorem stripe_seven_tail (m : Nat) (v : Fin 128)
    (hv : (v.val ≠ 13 ∨ m % 2 = 0) ∧ (v.val ≠ 27 ∨ m % 2 = 1) ∧
      (v.val ≠ 54 ∨ m % 2 = 0) ∧ (v.val ≠ 109 ∨ m % 2 = 1) ∧ (v.val ≠ 97 ∨ m % 2 = 0)) :
    ∃ d, 1 ≤ d ∧ d ≤ m + 9 ∧
      (∀ k, 1 ≤ k → k < d → row7 m v.val k = stripe k) ∧
      row7 m v.val d ≠ stripe d ∧
      ∃ t, t ≤ d - 1 + 31 ∧ t % 2 = 0 ∧ zrow (row7 m v.val) t 1 = false := by
  obtain ⟨v, hv128⟩ := v
  have hsplit : (0 ≤ v ∧ v < 16) ∨ (16 ≤ v ∧ v < 32) ∨ (32 ≤ v ∧ v < 48) ∨ (48 ≤ v ∧ v < 64) ∨
      (64 ≤ v ∧ v < 80) ∨ (80 ≤ v ∧ v < 96) ∨ (96 ≤ v ∧ v < 112) ∨ (112 ≤ v ∧ v < 128) := by omega
  rcases Nat.mod_two_eq_zero_or_one m with hq | hq <;>
    rcases hsplit with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact stripe_seven_q0_b0 m v hq h1 h2 hv
  · exact stripe_seven_q0_b1 m v hq h1 h2 hv
  · exact stripe_seven_q0_b2 m v hq h1 h2 hv
  · exact stripe_seven_q0_b3 m v hq h1 h2 hv
  · exact stripe_seven_q0_b4 m v hq h1 h2 hv
  · exact stripe_seven_q0_b5 m v hq h1 h2 hv
  · exact stripe_seven_q0_b6 m v hq h1 h2 hv
  · exact stripe_seven_q0_b7 m v hq h1 h2 hv
  · exact stripe_seven_q1_b0 m v hq h1 h2 hv
  · exact stripe_seven_q1_b1 m v hq h1 h2 hv
  · exact stripe_seven_q1_b2 m v hq h1 h2 hv
  · exact stripe_seven_q1_b3 m v hq h1 h2 hv
  · exact stripe_seven_q1_b4 m v hq h1 h2 hv
  · exact stripe_seven_q1_b5 m v hq h1 h2 hv
  · exact stripe_seven_q1_b6 m v hq h1 h2 hv
  · exact stripe_seven_q1_b7 m v hq h1 h2 hv

theorem row7_13_all_odd (m : Nat) (hq : m % 2 = 1) :
    ∃ d, 1 ≤ d ∧ d ≤ m + 9 ∧
      (∀ k, 1 ≤ k → k < d → row7 m 13 k = stripe k) ∧
      row7 m 13 d ≠ stripe d ∧
      ∃ t, t ≤ d - 1 + 45 ∧ t % 2 = 0 ∧ zrow (row7 m 13) t 1 = false :=
  family7_of_class m 1 1 46 45 45 2097152 13 hq (by decide) (by decide) (by decide) (by decide)
    (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cycle13_complete))

theorem row7_27_all_even (m : Nat) (hq : m % 2 = 0) :
    ∃ d, 1 ≤ d ∧ d ≤ m + 9 ∧
      (∀ k, 1 ≤ k → k < d → row7 m 27 k = stripe k) ∧
      row7 m 27 d ≠ stripe d ∧
      ∃ t, t ≤ d - 1 + 45 ∧ t % 2 = 0 ∧ zrow (row7 m 27) t 1 = false :=
  family7_of_class m 0 2 46 45 45 2097152 27 hq (by decide) (by decide) (by decide) (by decide)
    (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cycle13_complete))

theorem row7_54_all_odd (m : Nat) (hq : m % 2 = 1) :
    ∃ d, 1 ≤ d ∧ d ≤ m + 9 ∧
      (∀ k, 1 ≤ k → k < d → row7 m 54 k = stripe k) ∧
      row7 m 54 d ≠ stripe d ∧
      ∃ t, t ≤ d - 1 + 45 ∧ t % 2 = 0 ∧ zrow (row7 m 54) t 1 = false :=
  family7_of_class m 1 3 46 45 45 2097152 54 hq (by decide) (by decide) (by decide) (by decide)
    (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cycle13_complete))

theorem row7_109_all_even (m : Nat) (hq : m % 2 = 0) :
    ∃ d, 1 ≤ d ∧ d ≤ m + 9 ∧
      (∀ k, 1 ≤ k → k < d → row7 m 109 k = stripe k) ∧
      row7 m 109 d ≠ stripe d ∧
      ∃ t, t ≤ d - 1 + 45 ∧ t % 2 = 0 ∧ zrow (row7 m 109) t 1 = false :=
  family7_of_class m 0 4 46 45 45 2097152 109 hq (by decide) (by decide) (by decide) (by decide)
    (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cycle13_complete))

theorem row7_97_all_odd (m : Nat) (hq : m % 2 = 1) :
    ∃ d, 1 ≤ d ∧ d ≤ m + 9 ∧
      (∀ k, 1 ≤ k → k < d → row7 m 97 k = stripe k) ∧
      row7 m 97 d ≠ stripe d ∧
      ∃ t, t ≤ d - 1 + 45 ∧ t % 2 = 0 ∧ zrow (row7 m 97) t 1 = false :=
  family7_of_class m 1 1 36 35 45 262144 97 hq (by decide) (by decide) (by decide) (by decide)
    (by decide +kernel) (Or.inr (cycle_congr (by decide +kernel) (by decide) cycle97_complete))

theorem stripe_seven_tail_complete (m : Nat) (v : Fin 128) :
    ∃ d, 1 ≤ d ∧ d ≤ m + 9 ∧
      (∀ k, 1 ≤ k → k < d → row7 m v.val k = stripe k) ∧
      row7 m v.val d ≠ stripe d ∧
      ∃ t, t ≤ d - 1 + 45 ∧ t % 2 = 0 ∧ zrow (row7 m v.val) t 1 = false := by
  by_cases h : (v.val ≠ 13 ∨ m % 2 = 0) ∧ (v.val ≠ 27 ∨ m % 2 = 1) ∧
      (v.val ≠ 54 ∨ m % 2 = 0) ∧ (v.val ≠ 109 ∨ m % 2 = 1) ∧ (v.val ≠ 97 ∨ m % 2 = 0)
  · obtain ⟨d, hd, hdm, hag, hdev, t, ht, he, hz⟩ := stripe_seven_tail m v h
    exact ⟨d, hd, hdm, hag, hdev, t, by omega, he, hz⟩
  · rcases (show (v.val = 13 ∧ m % 2 = 1) ∨ (v.val = 27 ∧ m % 2 = 0) ∨
        (v.val = 54 ∧ m % 2 = 1) ∨ (v.val = 109 ∧ m % 2 = 0) ∨ (v.val = 97 ∧ m % 2 = 1) by omega)
      with ⟨hv, hq⟩ | ⟨hv, hq⟩ | ⟨hv, hq⟩ | ⟨hv, hq⟩ | ⟨hv, hq⟩
    · rw [hv]; exact row7_13_all_odd m hq
    · rw [hv]; exact row7_27_all_even m hq
    · rw [hv]; exact row7_54_all_odd m hq
    · rw [hv]; exact row7_109_all_even m hq
    · rw [hv]; exact row7_97_all_odd m hq

end Rule30ZeroBoundaryStripeSixSeven
end Ruliology.CellularAutomata
