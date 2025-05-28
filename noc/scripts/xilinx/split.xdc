create_clock -period 1.000 -name clk -waveform {0.000 0.5} [get_ports clk]
create_pblock {pblock_level_3_08}
resize_pblock [get_pblocks {pblock_level_3_08}] -add {CLOCKREGION_X0Y0:CLOCKREGION_X5Y14}
add_cells_to_pblock [get_pblocks {pblock_level_3_08}] [get_cells -quiet [list {n2.ls[3].ms[0].ns[0].pi_level.sb}]]
add_cells_to_pblock [get_pblocks {pblock_level_3_08}] [get_cells -quiet [list {n2.ls[3].ms[0].ns[1].pi_level.sb}]]
add_cells_to_pblock [get_pblocks {pblock_level_3_08}] [get_cells -quiet [list {n2.ls[3].ms[0].ns[2].pi_level.sb}]]
add_cells_to_pblock [get_pblocks {pblock_level_3_08}] [get_cells -quiet [list {n2.ls[3].ms[0].ns[3].pi_level.sb}]]
add_cells_to_pblock [get_pblocks {pblock_level_3_08}] [get_cells -quiet [list {n2.ls[3].ms[0].ns[4].pi_level.sb}]]
add_cells_to_pblock [get_pblocks {pblock_level_3_08}] [get_cells -quiet [list {n2.ls[3].ms[0].ns[5].pi_level.sb}]]
add_cells_to_pblock [get_pblocks {pblock_level_3_08}] [get_cells -quiet [list {n2.ls[3].ms[0].ns[6].pi_level.sb}]]
add_cells_to_pblock [get_pblocks {pblock_level_3_08}] [get_cells -quiet [list {n2.ls[3].ms[0].ns[7].pi_level.sb}]]
create_pblock {pblock_level_2_04}
resize_pblock [get_pblocks {pblock_level_2_04}] -add {CLOCKREGION_X0Y0:CLOCKREGION_X5Y7}
add_cells_to_pblock [get_pblocks {pblock_level_2_04}] [get_cells -quiet [list {n2.ls[2].ms[0].ns[0].pi_level.sb}]]
add_cells_to_pblock [get_pblocks {pblock_level_2_04}] [get_cells -quiet [list {n2.ls[2].ms[0].ns[1].pi_level.sb}]]
add_cells_to_pblock [get_pblocks {pblock_level_2_04}] [get_cells -quiet [list {n2.ls[2].ms[0].ns[2].pi_level.sb}]]
add_cells_to_pblock [get_pblocks {pblock_level_2_04}] [get_cells -quiet [list {n2.ls[2].ms[0].ns[3].pi_level.sb}]]
create_pblock {pblock_level_1_02}
resize_pblock [get_pblocks {pblock_level_1_02}] -add {CLOCKREGION_X0Y0:CLOCKREGION_X2Y7}
add_cells_to_pblock [get_pblocks {pblock_level_1_02}] [get_cells -quiet [list {n2.ls[1].ms[0].ns[0].pi_level.sb}]]
add_cells_to_pblock [get_pblocks {pblock_level_1_02}] [get_cells -quiet [list {n2.ls[1].ms[0].ns[1].pi_level.sb}]]
create_pblock {pblock_level_0_01}
resize_pblock [get_pblocks {pblock_level_0_01}] -add {CLOCKREGION_X0Y0:CLOCKREGION_X2Y3}
add_cells_to_pblock [get_pblocks {pblock_level_0_01}] [get_cells -quiet [list {xs[0].pi_level0.sb}]]
create_pblock {pblock_level_0_12}
resize_pblock [get_pblocks {pblock_level_0_12}] -add {CLOCKREGION_X0Y3:CLOCKREGION_X2Y7}
add_cells_to_pblock [get_pblocks {pblock_level_0_12}] [get_cells -quiet [list {xs[1].pi_level0.sb}]]
create_pblock {pblock_level_1_24}
resize_pblock [get_pblocks {pblock_level_1_24}] -add {CLOCKREGION_X2Y0:CLOCKREGION_X5Y7}
add_cells_to_pblock [get_pblocks {pblock_level_1_24}] [get_cells -quiet [list {n2.ls[1].ms[1].ns[0].pi_level.sb}]]
add_cells_to_pblock [get_pblocks {pblock_level_1_24}] [get_cells -quiet [list {n2.ls[1].ms[1].ns[1].pi_level.sb}]]
create_pblock {pblock_level_0_23}
resize_pblock [get_pblocks {pblock_level_0_23}] -add {CLOCKREGION_X2Y0:CLOCKREGION_X5Y3}
add_cells_to_pblock [get_pblocks {pblock_level_0_23}] [get_cells -quiet [list {xs[2].pi_level0.sb}]]
create_pblock {pblock_level_0_34}
resize_pblock [get_pblocks {pblock_level_0_34}] -add {CLOCKREGION_X2Y3:CLOCKREGION_X5Y7}
add_cells_to_pblock [get_pblocks {pblock_level_0_34}] [get_cells -quiet [list {xs[3].pi_level0.sb}]]
create_pblock {pblock_level_2_48}
resize_pblock [get_pblocks {pblock_level_2_48}] -add {CLOCKREGION_X0Y7:CLOCKREGION_X5Y14}
add_cells_to_pblock [get_pblocks {pblock_level_2_48}] [get_cells -quiet [list {n2.ls[2].ms[1].ns[0].pi_level.sb}]]
add_cells_to_pblock [get_pblocks {pblock_level_2_48}] [get_cells -quiet [list {n2.ls[2].ms[1].ns[1].pi_level.sb}]]
add_cells_to_pblock [get_pblocks {pblock_level_2_48}] [get_cells -quiet [list {n2.ls[2].ms[1].ns[2].pi_level.sb}]]
add_cells_to_pblock [get_pblocks {pblock_level_2_48}] [get_cells -quiet [list {n2.ls[2].ms[1].ns[3].pi_level.sb}]]
create_pblock {pblock_level_1_46}
resize_pblock [get_pblocks {pblock_level_1_46}] -add {CLOCKREGION_X0Y7:CLOCKREGION_X2Y14}
add_cells_to_pblock [get_pblocks {pblock_level_1_46}] [get_cells -quiet [list {n2.ls[1].ms[2].ns[0].pi_level.sb}]]
add_cells_to_pblock [get_pblocks {pblock_level_1_46}] [get_cells -quiet [list {n2.ls[1].ms[2].ns[1].pi_level.sb}]]
create_pblock {pblock_level_0_45}
resize_pblock [get_pblocks {pblock_level_0_45}] -add {CLOCKREGION_X0Y7:CLOCKREGION_X2Y10}
add_cells_to_pblock [get_pblocks {pblock_level_0_45}] [get_cells -quiet [list {xs[4].pi_level0.sb}]]
create_pblock {pblock_level_0_56}
resize_pblock [get_pblocks {pblock_level_0_56}] -add {CLOCKREGION_X0Y10:CLOCKREGION_X2Y14}
add_cells_to_pblock [get_pblocks {pblock_level_0_56}] [get_cells -quiet [list {xs[5].pi_level0.sb}]]
create_pblock {pblock_level_1_68}
resize_pblock [get_pblocks {pblock_level_1_68}] -add {CLOCKREGION_X2Y7:CLOCKREGION_X5Y14}
add_cells_to_pblock [get_pblocks {pblock_level_1_68}] [get_cells -quiet [list {n2.ls[1].ms[3].ns[0].pi_level.sb}]]
add_cells_to_pblock [get_pblocks {pblock_level_1_68}] [get_cells -quiet [list {n2.ls[1].ms[3].ns[1].pi_level.sb}]]
create_pblock {pblock_level_0_67}
resize_pblock [get_pblocks {pblock_level_0_67}] -add {CLOCKREGION_X2Y7:CLOCKREGION_X5Y10}
add_cells_to_pblock [get_pblocks {pblock_level_0_67}] [get_cells -quiet [list {xs[6].pi_level0.sb}]]
create_pblock {pblock_level_0_78}
resize_pblock [get_pblocks {pblock_level_0_78}] -add {CLOCKREGION_X2Y10:CLOCKREGION_X5Y14}
add_cells_to_pblock [get_pblocks {pblock_level_0_78}] [get_cells -quiet [list {xs[7].pi_level0.sb}]]
