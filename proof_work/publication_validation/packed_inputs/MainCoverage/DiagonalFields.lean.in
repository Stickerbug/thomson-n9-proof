import MainCoverage.DiagFields000
import MainCoverage.DiagFields001
import MainCoverage.DiagFields002
import MainCoverage.DiagFields003
import MainCoverage.DiagFields004
import MainCoverage.DiagFields005
import MainCoverage.DiagFields006
import MainCoverage.DiagFields007
import MainCoverage.DiagFields008
import MainCoverage.DiagFields009
import MainCoverage.DiagFields010
import MainCoverage.DiagFields011
import MainCoverage.DiagFields012
import MainCoverage.DiagFields013
import MainCoverage.DiagFields014
import MainCoverage.DiagFields015
import MainCoverage.DiagFields016
import MainCoverage.DiagFields017
import MainCoverage.DiagFields018
import MainCoverage.DiagFields019
import MainCoverage.DiagFields020
import MainCoverage.DiagFields021
import MainCoverage.DiagFields022
import MainCoverage.DiagFields023
import MainCoverage.DiagFields024
import MainCoverage.DiagFields025
import MainCoverage.DiagFields026
import MainCoverage.DiagFields027
import MainCoverage.DiagFields028
import MainCoverage.DiagFields029
import MainCoverage.DiagFields030
import MainCoverage.DiagFields031
import MainCoverage.DiagFields032
import MainCoverage.DiagFields033
import MainCoverage.DiagFields034
import MainCoverage.DiagFields035
import MainCoverage.DiagFields036
import MainCoverage.DiagFields037
import MainCoverage.DiagFields038
import MainCoverage.DiagFields039
import MainCoverage.DiagFields040
import MainCoverage.DiagFields041
import MainCoverage.DiagFields042
import MainCoverage.DiagFields043
import MainCoverage.DiagFields044
import MainCoverage.DiagFields045
import MainCoverage.DiagFields046
import MainCoverage.DiagFields047
import MainCoverage.DiagFields048
import MainCoverage.DiagFields049
import MainCoverage.DiagFields050
import MainCoverage.DiagFields051
import MainCoverage.DiagFields052
import MainCoverage.DiagFields053
import MainCoverage.DiagFields054
import MainCoverage.DiagFields055
import MainCoverage.DiagFields056
import MainCoverage.DiagFields057
import MainCoverage.DiagFields058
import MainCoverage.DiagFields059
import MainCoverage.DiagFields060
import MainCoverage.DiagFields061
import MainCoverage.DiagFields062
import MainCoverage.DiagFields063
import MainCoverage.DiagFields064
import MainCoverage.DiagFields065
import MainCoverage.DiagFields066
import MainCoverage.DiagFields067
import MainCoverage.DiagFields068
import MainCoverage.DiagFields069
import MainCoverage.DiagFields070
import MainCoverage.DiagFields071
import MainCoverage.DiagFields072
import MainCoverage.DiagFields073
import MainCoverage.DiagFields074
import MainCoverage.DiagFields075
namespace ThomsonNine.PackedMain
theorem bounded_block (P : ℕ → Prop) (lo count : ℕ) (h : ∀ i : Fin count, P (lo+i.val))
    (id : ℕ) (hl : lo ≤ id) (hr : id < lo+count) : P id := by
  have hi : id-lo<count := by omega
  have he : lo+(id-lo)=id := by omega
  simpa only [he] using h ⟨id-lo,hi⟩
theorem all_diagonal_fields (id : ℕ) (hid : id<4816) : diagonalOK diagonalLookup diagonalRootWord id=true := by
  by_cases h0 : id<64
  · exact bounded_block (fun n => diagonalOK diagonalLookup diagonalRootWord n=true) 0 64 diagonal_fields_0 id (by omega) (by omega)
  by_cases h1 : id<128
  · exact bounded_block (fun n => diagonalOK diagonalLookup diagonalRootWord n=true) 64 64 diagonal_fields_1 id (by omega) (by omega)
  by_cases h2 : id<192
  · exact bounded_block (fun n => diagonalOK diagonalLookup diagonalRootWord n=true) 128 64 diagonal_fields_2 id (by omega) (by omega)
  by_cases h3 : id<256
  · exact bounded_block (fun n => diagonalOK diagonalLookup diagonalRootWord n=true) 192 64 diagonal_fields_3 id (by omega) (by omega)
  by_cases h4 : id<320
  · exact bounded_block (fun n => diagonalOK diagonalLookup diagonalRootWord n=true) 256 64 diagonal_fields_4 id (by omega) (by omega)
  by_cases h5 : id<384
  · exact bounded_block (fun n => diagonalOK diagonalLookup diagonalRootWord n=true) 320 64 diagonal_fields_5 id (by omega) (by omega)
  by_cases h6 : id<448
  · exact bounded_block (fun n => diagonalOK diagonalLookup diagonalRootWord n=true) 384 64 diagonal_fields_6 id (by omega) (by omega)
  by_cases h7 : id<512
  · exact bounded_block (fun n => diagonalOK diagonalLookup diagonalRootWord n=true) 448 64 diagonal_fields_7 id (by omega) (by omega)
  by_cases h8 : id<576
  · exact bounded_block (fun n => diagonalOK diagonalLookup diagonalRootWord n=true) 512 64 diagonal_fields_8 id (by omega) (by omega)
  by_cases h9 : id<640
  · exact bounded_block (fun n => diagonalOK diagonalLookup diagonalRootWord n=true) 576 64 diagonal_fields_9 id (by omega) (by omega)
  by_cases h10 : id<704
  · exact bounded_block (fun n => diagonalOK diagonalLookup diagonalRootWord n=true) 640 64 diagonal_fields_10 id (by omega) (by omega)
  by_cases h11 : id<768
  · exact bounded_block (fun n => diagonalOK diagonalLookup diagonalRootWord n=true) 704 64 diagonal_fields_11 id (by omega) (by omega)
  by_cases h12 : id<832
  · exact bounded_block (fun n => diagonalOK diagonalLookup diagonalRootWord n=true) 768 64 diagonal_fields_12 id (by omega) (by omega)
  by_cases h13 : id<896
  · exact bounded_block (fun n => diagonalOK diagonalLookup diagonalRootWord n=true) 832 64 diagonal_fields_13 id (by omega) (by omega)
  by_cases h14 : id<960
  · exact bounded_block (fun n => diagonalOK diagonalLookup diagonalRootWord n=true) 896 64 diagonal_fields_14 id (by omega) (by omega)
  by_cases h15 : id<1024
  · exact bounded_block (fun n => diagonalOK diagonalLookup diagonalRootWord n=true) 960 64 diagonal_fields_15 id (by omega) (by omega)
  by_cases h16 : id<1088
  · exact bounded_block (fun n => diagonalOK diagonalLookup diagonalRootWord n=true) 1024 64 diagonal_fields_16 id (by omega) (by omega)
  by_cases h17 : id<1152
  · exact bounded_block (fun n => diagonalOK diagonalLookup diagonalRootWord n=true) 1088 64 diagonal_fields_17 id (by omega) (by omega)
  by_cases h18 : id<1216
  · exact bounded_block (fun n => diagonalOK diagonalLookup diagonalRootWord n=true) 1152 64 diagonal_fields_18 id (by omega) (by omega)
  by_cases h19 : id<1280
  · exact bounded_block (fun n => diagonalOK diagonalLookup diagonalRootWord n=true) 1216 64 diagonal_fields_19 id (by omega) (by omega)
  by_cases h20 : id<1344
  · exact bounded_block (fun n => diagonalOK diagonalLookup diagonalRootWord n=true) 1280 64 diagonal_fields_20 id (by omega) (by omega)
  by_cases h21 : id<1408
  · exact bounded_block (fun n => diagonalOK diagonalLookup diagonalRootWord n=true) 1344 64 diagonal_fields_21 id (by omega) (by omega)
  by_cases h22 : id<1472
  · exact bounded_block (fun n => diagonalOK diagonalLookup diagonalRootWord n=true) 1408 64 diagonal_fields_22 id (by omega) (by omega)
  by_cases h23 : id<1536
  · exact bounded_block (fun n => diagonalOK diagonalLookup diagonalRootWord n=true) 1472 64 diagonal_fields_23 id (by omega) (by omega)
  by_cases h24 : id<1600
  · exact bounded_block (fun n => diagonalOK diagonalLookup diagonalRootWord n=true) 1536 64 diagonal_fields_24 id (by omega) (by omega)
  by_cases h25 : id<1664
  · exact bounded_block (fun n => diagonalOK diagonalLookup diagonalRootWord n=true) 1600 64 diagonal_fields_25 id (by omega) (by omega)
  by_cases h26 : id<1728
  · exact bounded_block (fun n => diagonalOK diagonalLookup diagonalRootWord n=true) 1664 64 diagonal_fields_26 id (by omega) (by omega)
  by_cases h27 : id<1792
  · exact bounded_block (fun n => diagonalOK diagonalLookup diagonalRootWord n=true) 1728 64 diagonal_fields_27 id (by omega) (by omega)
  by_cases h28 : id<1856
  · exact bounded_block (fun n => diagonalOK diagonalLookup diagonalRootWord n=true) 1792 64 diagonal_fields_28 id (by omega) (by omega)
  by_cases h29 : id<1920
  · exact bounded_block (fun n => diagonalOK diagonalLookup diagonalRootWord n=true) 1856 64 diagonal_fields_29 id (by omega) (by omega)
  by_cases h30 : id<1984
  · exact bounded_block (fun n => diagonalOK diagonalLookup diagonalRootWord n=true) 1920 64 diagonal_fields_30 id (by omega) (by omega)
  by_cases h31 : id<2048
  · exact bounded_block (fun n => diagonalOK diagonalLookup diagonalRootWord n=true) 1984 64 diagonal_fields_31 id (by omega) (by omega)
  by_cases h32 : id<2112
  · exact bounded_block (fun n => diagonalOK diagonalLookup diagonalRootWord n=true) 2048 64 diagonal_fields_32 id (by omega) (by omega)
  by_cases h33 : id<2176
  · exact bounded_block (fun n => diagonalOK diagonalLookup diagonalRootWord n=true) 2112 64 diagonal_fields_33 id (by omega) (by omega)
  by_cases h34 : id<2240
  · exact bounded_block (fun n => diagonalOK diagonalLookup diagonalRootWord n=true) 2176 64 diagonal_fields_34 id (by omega) (by omega)
  by_cases h35 : id<2304
  · exact bounded_block (fun n => diagonalOK diagonalLookup diagonalRootWord n=true) 2240 64 diagonal_fields_35 id (by omega) (by omega)
  by_cases h36 : id<2368
  · exact bounded_block (fun n => diagonalOK diagonalLookup diagonalRootWord n=true) 2304 64 diagonal_fields_36 id (by omega) (by omega)
  by_cases h37 : id<2432
  · exact bounded_block (fun n => diagonalOK diagonalLookup diagonalRootWord n=true) 2368 64 diagonal_fields_37 id (by omega) (by omega)
  by_cases h38 : id<2496
  · exact bounded_block (fun n => diagonalOK diagonalLookup diagonalRootWord n=true) 2432 64 diagonal_fields_38 id (by omega) (by omega)
  by_cases h39 : id<2560
  · exact bounded_block (fun n => diagonalOK diagonalLookup diagonalRootWord n=true) 2496 64 diagonal_fields_39 id (by omega) (by omega)
  by_cases h40 : id<2624
  · exact bounded_block (fun n => diagonalOK diagonalLookup diagonalRootWord n=true) 2560 64 diagonal_fields_40 id (by omega) (by omega)
  by_cases h41 : id<2688
  · exact bounded_block (fun n => diagonalOK diagonalLookup diagonalRootWord n=true) 2624 64 diagonal_fields_41 id (by omega) (by omega)
  by_cases h42 : id<2752
  · exact bounded_block (fun n => diagonalOK diagonalLookup diagonalRootWord n=true) 2688 64 diagonal_fields_42 id (by omega) (by omega)
  by_cases h43 : id<2816
  · exact bounded_block (fun n => diagonalOK diagonalLookup diagonalRootWord n=true) 2752 64 diagonal_fields_43 id (by omega) (by omega)
  by_cases h44 : id<2880
  · exact bounded_block (fun n => diagonalOK diagonalLookup diagonalRootWord n=true) 2816 64 diagonal_fields_44 id (by omega) (by omega)
  by_cases h45 : id<2944
  · exact bounded_block (fun n => diagonalOK diagonalLookup diagonalRootWord n=true) 2880 64 diagonal_fields_45 id (by omega) (by omega)
  by_cases h46 : id<3008
  · exact bounded_block (fun n => diagonalOK diagonalLookup diagonalRootWord n=true) 2944 64 diagonal_fields_46 id (by omega) (by omega)
  by_cases h47 : id<3072
  · exact bounded_block (fun n => diagonalOK diagonalLookup diagonalRootWord n=true) 3008 64 diagonal_fields_47 id (by omega) (by omega)
  by_cases h48 : id<3136
  · exact bounded_block (fun n => diagonalOK diagonalLookup diagonalRootWord n=true) 3072 64 diagonal_fields_48 id (by omega) (by omega)
  by_cases h49 : id<3200
  · exact bounded_block (fun n => diagonalOK diagonalLookup diagonalRootWord n=true) 3136 64 diagonal_fields_49 id (by omega) (by omega)
  by_cases h50 : id<3264
  · exact bounded_block (fun n => diagonalOK diagonalLookup diagonalRootWord n=true) 3200 64 diagonal_fields_50 id (by omega) (by omega)
  by_cases h51 : id<3328
  · exact bounded_block (fun n => diagonalOK diagonalLookup diagonalRootWord n=true) 3264 64 diagonal_fields_51 id (by omega) (by omega)
  by_cases h52 : id<3392
  · exact bounded_block (fun n => diagonalOK diagonalLookup diagonalRootWord n=true) 3328 64 diagonal_fields_52 id (by omega) (by omega)
  by_cases h53 : id<3456
  · exact bounded_block (fun n => diagonalOK diagonalLookup diagonalRootWord n=true) 3392 64 diagonal_fields_53 id (by omega) (by omega)
  by_cases h54 : id<3520
  · exact bounded_block (fun n => diagonalOK diagonalLookup diagonalRootWord n=true) 3456 64 diagonal_fields_54 id (by omega) (by omega)
  by_cases h55 : id<3584
  · exact bounded_block (fun n => diagonalOK diagonalLookup diagonalRootWord n=true) 3520 64 diagonal_fields_55 id (by omega) (by omega)
  by_cases h56 : id<3648
  · exact bounded_block (fun n => diagonalOK diagonalLookup diagonalRootWord n=true) 3584 64 diagonal_fields_56 id (by omega) (by omega)
  by_cases h57 : id<3712
  · exact bounded_block (fun n => diagonalOK diagonalLookup diagonalRootWord n=true) 3648 64 diagonal_fields_57 id (by omega) (by omega)
  by_cases h58 : id<3776
  · exact bounded_block (fun n => diagonalOK diagonalLookup diagonalRootWord n=true) 3712 64 diagonal_fields_58 id (by omega) (by omega)
  by_cases h59 : id<3840
  · exact bounded_block (fun n => diagonalOK diagonalLookup diagonalRootWord n=true) 3776 64 diagonal_fields_59 id (by omega) (by omega)
  by_cases h60 : id<3904
  · exact bounded_block (fun n => diagonalOK diagonalLookup diagonalRootWord n=true) 3840 64 diagonal_fields_60 id (by omega) (by omega)
  by_cases h61 : id<3968
  · exact bounded_block (fun n => diagonalOK diagonalLookup diagonalRootWord n=true) 3904 64 diagonal_fields_61 id (by omega) (by omega)
  by_cases h62 : id<4032
  · exact bounded_block (fun n => diagonalOK diagonalLookup diagonalRootWord n=true) 3968 64 diagonal_fields_62 id (by omega) (by omega)
  by_cases h63 : id<4096
  · exact bounded_block (fun n => diagonalOK diagonalLookup diagonalRootWord n=true) 4032 64 diagonal_fields_63 id (by omega) (by omega)
  by_cases h64 : id<4160
  · exact bounded_block (fun n => diagonalOK diagonalLookup diagonalRootWord n=true) 4096 64 diagonal_fields_64 id (by omega) (by omega)
  by_cases h65 : id<4224
  · exact bounded_block (fun n => diagonalOK diagonalLookup diagonalRootWord n=true) 4160 64 diagonal_fields_65 id (by omega) (by omega)
  by_cases h66 : id<4288
  · exact bounded_block (fun n => diagonalOK diagonalLookup diagonalRootWord n=true) 4224 64 diagonal_fields_66 id (by omega) (by omega)
  by_cases h67 : id<4352
  · exact bounded_block (fun n => diagonalOK diagonalLookup diagonalRootWord n=true) 4288 64 diagonal_fields_67 id (by omega) (by omega)
  by_cases h68 : id<4416
  · exact bounded_block (fun n => diagonalOK diagonalLookup diagonalRootWord n=true) 4352 64 diagonal_fields_68 id (by omega) (by omega)
  by_cases h69 : id<4480
  · exact bounded_block (fun n => diagonalOK diagonalLookup diagonalRootWord n=true) 4416 64 diagonal_fields_69 id (by omega) (by omega)
  by_cases h70 : id<4544
  · exact bounded_block (fun n => diagonalOK diagonalLookup diagonalRootWord n=true) 4480 64 diagonal_fields_70 id (by omega) (by omega)
  by_cases h71 : id<4608
  · exact bounded_block (fun n => diagonalOK diagonalLookup diagonalRootWord n=true) 4544 64 diagonal_fields_71 id (by omega) (by omega)
  by_cases h72 : id<4672
  · exact bounded_block (fun n => diagonalOK diagonalLookup diagonalRootWord n=true) 4608 64 diagonal_fields_72 id (by omega) (by omega)
  by_cases h73 : id<4736
  · exact bounded_block (fun n => diagonalOK diagonalLookup diagonalRootWord n=true) 4672 64 diagonal_fields_73 id (by omega) (by omega)
  by_cases h74 : id<4800
  · exact bounded_block (fun n => diagonalOK diagonalLookup diagonalRootWord n=true) 4736 64 diagonal_fields_74 id (by omega) (by omega)
  exact bounded_block (fun n => diagonalOK diagonalLookup diagonalRootWord n=true) 4800 16 diagonal_fields_75 id (by omega) (by omega)
end ThomsonNine.PackedMain
