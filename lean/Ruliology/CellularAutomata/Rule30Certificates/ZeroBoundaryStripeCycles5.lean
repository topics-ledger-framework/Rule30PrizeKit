module

public import Ruliology.CellularAutomata.Rule30ZeroBoundaryStripeFront

@[expose] public section

namespace Ruliology.CellularAutomata
namespace Rule30ZeroBoundaryStripeFront.StripeCycles5

open Rule30ZeroBoundaryStripeFront

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem cyc7_65_s0 : seg 10 9 1 65 0 64 0 65 0 = true := by decide +kernel
theorem cyc7_65_path : PathOK 10 9 1 0 (65, 0) (65, 0) 64 :=
  seg_sound 10 9 1 65 0 64 0 65 0 cyc7_65_s0
theorem cyc7_65 : Cycle 10 9 65 0 64 :=
  ⟨by decide, by decide, cyc7_65_path.1, cyc7_65_path.2⟩

theorem cyc7_67_s0 : seg 8 7 1 67 0 32 0 67 0 = true := by decide +kernel
theorem cyc7_67_path : PathOK 8 7 1 0 (67, 0) (67, 0) 32 :=
  seg_sound 8 7 1 67 0 32 0 67 0 cyc7_67_s0
theorem cyc7_67 : Cycle 8 7 67 0 32 :=
  ⟨by decide, by decide, cyc7_67_path.1, cyc7_67_path.2⟩

theorem cyc7_69_s0 : seg 18 17 1 69 0 512 0 69 0 = true := by decide +kernel
theorem cyc7_69_path : PathOK 18 17 1 0 (69, 0) (69, 0) 512 :=
  seg_sound 18 17 1 69 0 512 0 69 0 cyc7_69_s0
theorem cyc7_69 : Cycle 18 17 69 0 512 :=
  ⟨by decide, by decide, cyc7_69_path.1, cyc7_69_path.2⟩

theorem cyc7_71_s0 : seg 10 9 1 71 0 32 0 71 0 = true := by decide +kernel
theorem cyc7_71_path : PathOK 10 9 1 0 (71, 0) (71, 0) 32 :=
  seg_sound 10 9 1 71 0 32 0 71 0 cyc7_71_s0
theorem cyc7_71 : Cycle 10 9 71 0 32 :=
  ⟨by decide, by decide, cyc7_71_path.1, cyc7_71_path.2⟩

theorem cyc7_73_s0 : seg 18 17 1 73 0 512 0 73 0 = true := by decide +kernel
theorem cyc7_73_path : PathOK 18 17 1 0 (73, 0) (73, 0) 512 :=
  seg_sound 18 17 1 73 0 512 0 73 0 cyc7_73_s0
theorem cyc7_73 : Cycle 18 17 73 0 512 :=
  ⟨by decide, by decide, cyc7_73_path.1, cyc7_73_path.2⟩

theorem cyc7_75_s0 : seg 10 9 1 75 0 64 0 75 0 = true := by decide +kernel
theorem cyc7_75_path : PathOK 10 9 1 0 (75, 0) (75, 0) 64 :=
  seg_sound 10 9 1 75 0 64 0 75 0 cyc7_75_s0
theorem cyc7_75 : Cycle 10 9 75 0 64 :=
  ⟨by decide, by decide, cyc7_75_path.1, cyc7_75_path.2⟩

theorem cyc7_77_s0 : seg 24 23 1 77 0 4096 0 77 0 = true := by decide +kernel
theorem cyc7_77_path : PathOK 24 23 1 0 (77, 0) (77, 0) 4096 :=
  seg_sound 24 23 1 77 0 4096 0 77 0 cyc7_77_s0
theorem cyc7_77 : Cycle 24 23 77 0 4096 :=
  ⟨by decide, by decide, cyc7_77_path.1, cyc7_77_path.2⟩

theorem cyc7_79_s0 : seg 16 15 1 79 0 512 0 79 0 = true := by decide +kernel
theorem cyc7_79_path : PathOK 16 15 1 0 (79, 0) (79, 0) 512 :=
  seg_sound 16 15 1 79 0 512 0 79 0 cyc7_79_s0
theorem cyc7_79 : Cycle 16 15 79 0 512 :=
  ⟨by decide, by decide, cyc7_79_path.1, cyc7_79_path.2⟩

theorem cyc7_81_s0 : seg 26 25 1 81 0 8192 0 81 0 = true := by decide +kernel
theorem cyc7_81_path : PathOK 26 25 1 0 (81, 0) (81, 0) 8192 :=
  seg_sound 26 25 1 81 0 8192 0 81 0 cyc7_81_s0
theorem cyc7_81 : Cycle 26 25 81 0 8192 :=
  ⟨by decide, by decide, cyc7_81_path.1, cyc7_81_path.2⟩

theorem cyc7_83_s0 : seg 20 19 1 83 0 2048 0 83 0 = true := by decide +kernel
theorem cyc7_83_path : PathOK 20 19 1 0 (83, 0) (83, 0) 2048 :=
  seg_sound 20 19 1 83 0 2048 0 83 0 cyc7_83_s0
theorem cyc7_83 : Cycle 20 19 83 0 2048 :=
  ⟨by decide, by decide, cyc7_83_path.1, cyc7_83_path.2⟩

theorem cyc7_85_s0 : seg 22 21 1 85 0 2048 0 85 0 = true := by decide +kernel
theorem cyc7_85_path : PathOK 22 21 1 0 (85, 0) (85, 0) 2048 :=
  seg_sound 22 21 1 85 0 2048 0 85 0 cyc7_85_s0
theorem cyc7_85 : Cycle 22 21 85 0 2048 :=
  ⟨by decide, by decide, cyc7_85_path.1, cyc7_85_path.2⟩

theorem cyc7_87_s0 : seg 18 17 1 87 0 1024 0 87 0 = true := by decide +kernel
theorem cyc7_87_path : PathOK 18 17 1 0 (87, 0) (87, 0) 1024 :=
  seg_sound 18 17 1 87 0 1024 0 87 0 cyc7_87_s0
theorem cyc7_87 : Cycle 18 17 87 0 1024 :=
  ⟨by decide, by decide, cyc7_87_path.1, cyc7_87_path.2⟩

theorem cyc7_89_s0 : seg 22 21 1 89 0 4096 0 89 0 = true := by decide +kernel
theorem cyc7_89_path : PathOK 22 21 1 0 (89, 0) (89, 0) 4096 :=
  seg_sound 22 21 1 89 0 4096 0 89 0 cyc7_89_s0
theorem cyc7_89 : Cycle 22 21 89 0 4096 :=
  ⟨by decide, by decide, cyc7_89_path.1, cyc7_89_path.2⟩

theorem cyc7_91_s0 : seg 22 21 1 91 0 4096 0 91 0 = true := by decide +kernel
theorem cyc7_91_path : PathOK 22 21 1 0 (91, 0) (91, 0) 4096 :=
  seg_sound 22 21 1 91 0 4096 0 91 0 cyc7_91_s0
theorem cyc7_91 : Cycle 22 21 91 0 4096 :=
  ⟨by decide, by decide, cyc7_91_path.1, cyc7_91_path.2⟩

theorem cyc7_93_s0 : seg 10 9 1 93 0 64 0 93 0 = true := by decide +kernel
theorem cyc7_93_path : PathOK 10 9 1 0 (93, 0) (93, 0) 64 :=
  seg_sound 10 9 1 93 0 64 0 93 0 cyc7_93_s0
theorem cyc7_93 : Cycle 10 9 93 0 64 :=
  ⟨by decide, by decide, cyc7_93_path.1, cyc7_93_path.2⟩

theorem cyc7_95_s0 : seg 10 9 1 95 0 64 0 95 0 = true := by decide +kernel
theorem cyc7_95_path : PathOK 10 9 1 0 (95, 0) (95, 0) 64 :=
  seg_sound 10 9 1 95 0 64 0 95 0 cyc7_95_s0
theorem cyc7_95 : Cycle 10 9 95 0 64 :=
  ⟨by decide, by decide, cyc7_95_path.1, cyc7_95_path.2⟩

theorem cyc7_99_s0 : seg 20 19 1 99 0 2048 0 99 0 = true := by decide +kernel
theorem cyc7_99_path : PathOK 20 19 1 0 (99, 0) (99, 0) 2048 :=
  seg_sound 20 19 1 99 0 2048 0 99 0 cyc7_99_s0
theorem cyc7_99 : Cycle 20 19 99 0 2048 :=
  ⟨by decide, by decide, cyc7_99_path.1, cyc7_99_path.2⟩

theorem cyc7_101_s0 : seg 30 29 1 805306469 0 8192 0 101 0 = true := by decide +kernel
theorem cyc7_101_s1 : seg 30 29 1 101 0 8192 8192 805306469 0 = true := by decide +kernel
theorem cyc7_101_path : PathOK 30 29 1 0 (101, 0) (101, 0) 16384 :=
  (path_append (seg_sound 30 29 1 805306469 0 8192 0 101 0 cyc7_101_s0)
    (seg_sound 30 29 1 101 0 8192 8192 805306469 0 cyc7_101_s1))
theorem cyc7_101 : Cycle 30 29 101 0 16384 :=
  ⟨by decide, by decide, cyc7_101_path.1, cyc7_101_path.2⟩

theorem cyc7_103_s0 : seg 10 9 1 103 0 32 0 103 0 = true := by decide +kernel
theorem cyc7_103_path : PathOK 10 9 1 0 (103, 0) (103, 0) 32 :=
  seg_sound 10 9 1 103 0 32 0 103 0 cyc7_103_s0
theorem cyc7_103 : Cycle 10 9 103 0 32 :=
  ⟨by decide, by decide, cyc7_103_path.1, cyc7_103_path.2⟩

theorem cyc7_105_s0 : seg 8 7 1 105 0 32 0 105 0 = true := by decide +kernel
theorem cyc7_105_path : PathOK 8 7 1 0 (105, 0) (105, 0) 32 :=
  seg_sound 8 7 1 105 0 32 0 105 0 cyc7_105_s0
theorem cyc7_105 : Cycle 8 7 105 0 32 :=
  ⟨by decide, by decide, cyc7_105_path.1, cyc7_105_path.2⟩

theorem cyc7_107_s0 : seg 10 9 1 107 0 64 0 107 0 = true := by decide +kernel
theorem cyc7_107_path : PathOK 10 9 1 0 (107, 0) (107, 0) 64 :=
  seg_sound 10 9 1 107 0 64 0 107 0 cyc7_107_s0
theorem cyc7_107 : Cycle 10 9 107 0 64 :=
  ⟨by decide, by decide, cyc7_107_path.1, cyc7_107_path.2⟩

theorem cyc7_109_s0 : seg 10 9 1 109 0 64 0 109 0 = true := by decide +kernel
theorem cyc7_109_path : PathOK 10 9 1 0 (109, 0) (109, 0) 64 :=
  seg_sound 10 9 1 109 0 64 0 109 0 cyc7_109_s0
theorem cyc7_109 : Cycle 10 9 109 0 64 :=
  ⟨by decide, by decide, cyc7_109_path.1, cyc7_109_path.2⟩

theorem cyc7_111_s0 : seg 24 23 1 111 0 1024 0 111 0 = true := by decide +kernel
theorem cyc7_111_path : PathOK 24 23 1 0 (111, 0) (111, 0) 1024 :=
  seg_sound 24 23 1 111 0 1024 0 111 0 cyc7_111_s0
theorem cyc7_111 : Cycle 24 23 111 0 1024 :=
  ⟨by decide, by decide, cyc7_111_path.1, cyc7_111_path.2⟩

theorem cyc7_113_s0 : seg 18 17 1 113 0 512 0 113 0 = true := by decide +kernel
theorem cyc7_113_path : PathOK 18 17 1 0 (113, 0) (113, 0) 512 :=
  seg_sound 18 17 1 113 0 512 0 113 0 cyc7_113_s0
theorem cyc7_113 : Cycle 18 17 113 0 512 :=
  ⟨by decide, by decide, cyc7_113_path.1, cyc7_113_path.2⟩

theorem cyc7_115_s0 : seg 24 23 1 115 0 2048 0 115 0 = true := by decide +kernel
theorem cyc7_115_path : PathOK 24 23 1 0 (115, 0) (115, 0) 2048 :=
  seg_sound 24 23 1 115 0 2048 0 115 0 cyc7_115_s0
theorem cyc7_115 : Cycle 24 23 115 0 2048 :=
  ⟨by decide, by decide, cyc7_115_path.1, cyc7_115_path.2⟩

theorem cyc7_117_s0 : seg 8 7 1 117 0 32 0 117 0 = true := by decide +kernel
theorem cyc7_117_path : PathOK 8 7 1 0 (117, 0) (117, 0) 32 :=
  seg_sound 8 7 1 117 0 32 0 117 0 cyc7_117_s0
theorem cyc7_117 : Cycle 8 7 117 0 32 :=
  ⟨by decide, by decide, cyc7_117_path.1, cyc7_117_path.2⟩

theorem cyc7_119_s0 : seg 10 9 1 119 0 32 0 119 0 = true := by decide +kernel
theorem cyc7_119_path : PathOK 10 9 1 0 (119, 0) (119, 0) 32 :=
  seg_sound 10 9 1 119 0 32 0 119 0 cyc7_119_s0
theorem cyc7_119 : Cycle 10 9 119 0 32 :=
  ⟨by decide, by decide, cyc7_119_path.1, cyc7_119_path.2⟩

theorem cyc7_121_s0 : seg 14 13 1 121 0 128 0 121 0 = true := by decide +kernel
theorem cyc7_121_path : PathOK 14 13 1 0 (121, 0) (121, 0) 128 :=
  seg_sound 14 13 1 121 0 128 0 121 0 cyc7_121_s0
theorem cyc7_121 : Cycle 14 13 121 0 128 :=
  ⟨by decide, by decide, cyc7_121_path.1, cyc7_121_path.2⟩

theorem cyc7_123_s0 : seg 10 9 1 123 0 64 0 123 0 = true := by decide +kernel
theorem cyc7_123_path : PathOK 10 9 1 0 (123, 0) (123, 0) 64 :=
  seg_sound 10 9 1 123 0 64 0 123 0 cyc7_123_s0
theorem cyc7_123 : Cycle 10 9 123 0 64 :=
  ⟨by decide, by decide, cyc7_123_path.1, cyc7_123_path.2⟩

theorem cyc7_125_s0 : seg 10 9 1 125 0 64 0 125 0 = true := by decide +kernel
theorem cyc7_125_path : PathOK 10 9 1 0 (125, 0) (125, 0) 64 :=
  seg_sound 10 9 1 125 0 64 0 125 0 cyc7_125_s0
theorem cyc7_125 : Cycle 10 9 125 0 64 :=
  ⟨by decide, by decide, cyc7_125_path.1, cyc7_125_path.2⟩

theorem cyc7_127_s0 : seg 22 21 1 127 0 1024 0 127 0 = true := by decide +kernel
theorem cyc7_127_path : PathOK 22 21 1 0 (127, 0) (127, 0) 1024 :=
  seg_sound 22 21 1 127 0 1024 0 127 0 cyc7_127_s0
theorem cyc7_127 : Cycle 22 21 127 0 1024 :=
  ⟨by decide, by decide, cyc7_127_path.1, cyc7_127_path.2⟩

end Rule30ZeroBoundaryStripeFront.StripeCycles5
end Ruliology.CellularAutomata
