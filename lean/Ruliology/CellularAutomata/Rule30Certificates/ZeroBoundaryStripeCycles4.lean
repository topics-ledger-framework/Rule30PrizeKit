module

public import Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront

@[expose] public section

namespace Ruliology.CellularAutomata
namespace Rule30ZeroBoundaryStripeFront.StripeCycles4

open Rule30ZeroBoundaryStripeFront

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem cyc6_33_s0 : seg 16 15 1 33 0 256 0 33 0 = true := by decide +kernel
theorem cyc6_33_path : PathOK 16 15 1 0 (33, 0) (33, 0) 256 :=
  seg_sound 16 15 1 33 0 256 0 33 0 cyc6_33_s0
theorem cyc6_33 : Cycle 16 15 33 0 256 :=
  ⟨by decide, by decide, cyc6_33_path.1, cyc6_33_path.2⟩

theorem cyc6_35_s0 : seg 20 19 1 35 0 512 0 35 0 = true := by decide +kernel
theorem cyc6_35_path : PathOK 20 19 1 0 (35, 0) (35, 0) 512 :=
  seg_sound 20 19 1 35 0 512 0 35 0 cyc6_35_s0
theorem cyc6_35 : Cycle 20 19 35 0 512 :=
  ⟨by decide, by decide, cyc6_35_path.1, cyc6_35_path.2⟩

theorem cyc6_37_s0 : seg 8 7 1 37 0 32 0 37 0 = true := by decide +kernel
theorem cyc6_37_path : PathOK 8 7 1 0 (37, 0) (37, 0) 32 :=
  seg_sound 8 7 1 37 0 32 0 37 0 cyc6_37_s0
theorem cyc6_37 : Cycle 8 7 37 0 32 :=
  ⟨by decide, by decide, cyc6_37_path.1, cyc6_37_path.2⟩

theorem cyc6_39_s0 : seg 28 27 1 39 0 8192 0 39 0 = true := by decide +kernel
theorem cyc6_39_path : PathOK 28 27 1 0 (39, 0) (39, 0) 8192 :=
  seg_sound 28 27 1 39 0 8192 0 39 0 cyc6_39_s0
theorem cyc6_39 : Cycle 28 27 39 0 8192 :=
  ⟨by decide, by decide, cyc6_39_path.1, cyc6_39_path.2⟩

theorem cyc6_41_s0 : seg 12 11 1 41 0 32 0 41 0 = true := by decide +kernel
theorem cyc6_41_path : PathOK 12 11 1 0 (41, 0) (41, 0) 32 :=
  seg_sound 12 11 1 41 0 32 0 41 0 cyc6_41_s0
theorem cyc6_41 : Cycle 12 11 41 0 32 :=
  ⟨by decide, by decide, cyc6_41_path.1, cyc6_41_path.2⟩

theorem cyc6_43_s0 : seg 10 9 1 43 0 64 0 43 0 = true := by decide +kernel
theorem cyc6_43_path : PathOK 10 9 1 0 (43, 0) (43, 0) 64 :=
  seg_sound 10 9 1 43 0 64 0 43 0 cyc6_43_s0
theorem cyc6_43 : Cycle 10 9 43 0 64 :=
  ⟨by decide, by decide, cyc6_43_path.1, cyc6_43_path.2⟩

theorem cyc6_45_s0 : seg 30 29 1 528482349 0 8192 0 45 0 = true := by decide +kernel
theorem cyc6_45_s1 : seg 30 29 1 603979821 0 8192 8192 528482349 0 = true := by decide +kernel
theorem cyc6_45_s2 : seg 30 29 1 729808941 0 8192 16384 603979821 0 = true := by decide +kernel
theorem cyc6_45_s3 : seg 30 29 1 45 0 8192 24576 729808941 0 = true := by decide +kernel
theorem cyc6_45_path : PathOK 30 29 1 0 (45, 0) (45, 0) 32768 :=
  (path_append (path_append (path_append (seg_sound 30 29 1 528482349 0 8192 0 45 0 cyc6_45_s0)
    (seg_sound 30 29 1 603979821 0 8192 8192 528482349 0 cyc6_45_s1))
    (seg_sound 30 29 1 729808941 0 8192 16384 603979821 0 cyc6_45_s2))
    (seg_sound 30 29 1 45 0 8192 24576 729808941 0 cyc6_45_s3))
theorem cyc6_45 : Cycle 30 29 45 0 32768 :=
  ⟨by decide, by decide, cyc6_45_path.1, cyc6_45_path.2⟩

theorem cyc6_47_s0 : seg 26 25 1 47 0 2048 0 47 0 = true := by decide +kernel
theorem cyc6_47_path : PathOK 26 25 1 0 (47, 0) (47, 0) 2048 :=
  seg_sound 26 25 1 47 0 2048 0 47 0 cyc6_47_s0
theorem cyc6_47 : Cycle 26 25 47 0 2048 :=
  ⟨by decide, by decide, cyc6_47_path.1, cyc6_47_path.2⟩

theorem cyc6_49_s0 : seg 10 9 1 49 0 64 0 49 0 = true := by decide +kernel
theorem cyc6_49_path : PathOK 10 9 1 0 (49, 0) (49, 0) 64 :=
  seg_sound 10 9 1 49 0 64 0 49 0 cyc6_49_s0
theorem cyc6_49 : Cycle 10 9 49 0 64 :=
  ⟨by decide, by decide, cyc6_49_path.1, cyc6_49_path.2⟩

theorem cyc6_51_s0 : seg 8 7 1 51 0 32 0 51 0 = true := by decide +kernel
theorem cyc6_51_path : PathOK 8 7 1 0 (51, 0) (51, 0) 32 :=
  seg_sound 8 7 1 51 0 32 0 51 0 cyc6_51_s0
theorem cyc6_51 : Cycle 8 7 51 0 32 :=
  ⟨by decide, by decide, cyc6_51_path.1, cyc6_51_path.2⟩

theorem cyc6_53_s0 : seg 10 9 1 53 0 32 0 53 0 = true := by decide +kernel
theorem cyc6_53_path : PathOK 10 9 1 0 (53, 0) (53, 0) 32 :=
  seg_sound 10 9 1 53 0 32 0 53 0 cyc6_53_s0
theorem cyc6_53 : Cycle 10 9 53 0 32 :=
  ⟨by decide, by decide, cyc6_53_path.1, cyc6_53_path.2⟩

theorem cyc6_55_s0 : seg 24 23 1 55 0 2048 0 55 0 = true := by decide +kernel
theorem cyc6_55_path : PathOK 24 23 1 0 (55, 0) (55, 0) 2048 :=
  seg_sound 24 23 1 55 0 2048 0 55 0 cyc6_55_s0
theorem cyc6_55 : Cycle 24 23 55 0 2048 :=
  ⟨by decide, by decide, cyc6_55_path.1, cyc6_55_path.2⟩

theorem cyc6_57_s0 : seg 30 29 1 671088697 0 8192 0 57 0 = true := by decide +kernel
theorem cyc6_57_s1 : seg 30 29 1 57 0 8192 8192 671088697 0 = true := by decide +kernel
theorem cyc6_57_path : PathOK 30 29 1 0 (57, 0) (57, 0) 16384 :=
  (path_append (seg_sound 30 29 1 671088697 0 8192 0 57 0 cyc6_57_s0)
    (seg_sound 30 29 1 57 0 8192 8192 671088697 0 cyc6_57_s1))
theorem cyc6_57 : Cycle 30 29 57 0 16384 :=
  ⟨by decide, by decide, cyc6_57_path.1, cyc6_57_path.2⟩

theorem cyc6_59_s0 : seg 10 9 1 59 0 64 0 59 0 = true := by decide +kernel
theorem cyc6_59_path : PathOK 10 9 1 0 (59, 0) (59, 0) 64 :=
  seg_sound 10 9 1 59 0 64 0 59 0 cyc6_59_s0
theorem cyc6_59 : Cycle 10 9 59 0 64 :=
  ⟨by decide, by decide, cyc6_59_path.1, cyc6_59_path.2⟩

theorem cyc6_61_s0 : seg 10 9 1 61 0 64 0 61 0 = true := by decide +kernel
theorem cyc6_61_path : PathOK 10 9 1 0 (61, 0) (61, 0) 64 :=
  seg_sound 10 9 1 61 0 64 0 61 0 cyc6_61_s0
theorem cyc6_61 : Cycle 10 9 61 0 64 :=
  ⟨by decide, by decide, cyc6_61_path.1, cyc6_61_path.2⟩

theorem cyc6_63_s0 : seg 16 15 1 63 0 256 0 63 0 = true := by decide +kernel
theorem cyc6_63_path : PathOK 16 15 1 0 (63, 0) (63, 0) 256 :=
  seg_sound 16 15 1 63 0 256 0 63 0 cyc6_63_s0
theorem cyc6_63 : Cycle 16 15 63 0 256 :=
  ⟨by decide, by decide, cyc6_63_path.1, cyc6_63_path.2⟩

end Rule30ZeroBoundaryStripeFront.StripeCycles4
end Ruliology.CellularAutomata
