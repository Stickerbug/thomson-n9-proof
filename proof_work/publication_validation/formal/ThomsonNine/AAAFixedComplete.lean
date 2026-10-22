import ThomsonNine.LocalSparseHessianAAA
import ThomsonNine.AAAFixedBounds00
import ThomsonNine.AAAFixedBounds01
import ThomsonNine.AAAFixedBounds02
import ThomsonNine.AAAFixedBounds03
import ThomsonNine.AAAFixedBounds04
import ThomsonNine.AAAFixedBounds05
import ThomsonNine.AAAFixedBounds06
import ThomsonNine.AAAFixedBounds07
import ThomsonNine.AAAFixedBounds08

noncomputable section
namespace ThomsonNine.AAAFixedComplete
open ThomsonNine.LocalSparseHessianAAA ThomsonNine.GatheredBinding
open ThomsonNine.AAAGroupedData ThomsonNine.AAAFixedData ThomsonNine.AAAFixedBounds

/-- Every archived target interval contains its full gathered coefficient,
conditional on one fixed source family and one fixed center. -/
theorem bounds : (k : TermIndex) →
    (precision : ℚ)*(coefficientInterval k).lo ≤ ((AAATreeData.computed k).lo : ℚ) ∧
    ((AAATreeData.computed k).hi : ℚ) ≤ (precision : ℚ)*(coefficientInterval k).hi
  | .t000 => bounds000
  | .t001 => bounds001
  | .t002 => bounds002
  | .t003 => bounds003
  | .t004 => bounds004
  | .t005 => bounds005
  | .t006 => bounds006
  | .t007 => bounds007
  | .t008 => bounds008
  | .t009 => bounds009
  | .t010 => bounds010
  | .t011 => bounds011
  | .t012 => bounds012
  | .t013 => bounds013
  | .t014 => bounds014
  | .t015 => bounds015
  | .t016 => bounds016
  | .t017 => bounds017
  | .t018 => bounds018
  | .t019 => bounds019
  | .t020 => bounds020
  | .t021 => bounds021
  | .t022 => bounds022
  | .t023 => bounds023
  | .t024 => bounds024
  | .t025 => bounds025
  | .t026 => bounds026
  | .t027 => bounds027
  | .t028 => bounds028
  | .t029 => bounds029
  | .t030 => bounds030
  | .t031 => bounds031
  | .t032 => bounds032
  | .t033 => bounds033
  | .t034 => bounds034
  | .t035 => bounds035
  | .t036 => bounds036
  | .t037 => bounds037
  | .t038 => bounds038
  | .t039 => bounds039
  | .t040 => bounds040
  | .t041 => bounds041
  | .t042 => bounds042
  | .t043 => bounds043
  | .t044 => bounds044
  | .t045 => bounds045
  | .t046 => bounds046
  | .t047 => bounds047
  | .t048 => bounds048
  | .t049 => bounds049
  | .t050 => bounds050
  | .t051 => bounds051
  | .t052 => bounds052
  | .t053 => bounds053
  | .t054 => bounds054
  | .t055 => bounds055
  | .t056 => bounds056
  | .t057 => bounds057
  | .t058 => bounds058
  | .t059 => bounds059
  | .t060 => bounds060
  | .t061 => bounds061
  | .t062 => bounds062
  | .t063 => bounds063
  | .t064 => bounds064
  | .t065 => bounds065
  | .t066 => bounds066
  | .t067 => bounds067
  | .t068 => bounds068
  | .t069 => bounds069
  | .t070 => bounds070
  | .t071 => bounds071
  | .t072 => bounds072
  | .t073 => bounds073
  | .t074 => bounds074
  | .t075 => bounds075
  | .t076 => bounds076
  | .t077 => bounds077
  | .t078 => bounds078
  | .t079 => bounds079
  | .t080 => bounds080
  | .t081 => bounds081
  | .t082 => bounds082
  | .t083 => bounds083
  | .t084 => bounds084
  | .t085 => bounds085
  | .t086 => bounds086
  | .t087 => bounds087
  | .t088 => bounds088
  | .t089 => bounds089
  | .t090 => bounds090
  | .t091 => bounds091
  | .t092 => bounds092
  | .t093 => bounds093
  | .t094 => bounds094
  | .t095 => bounds095
  | .t096 => bounds096
  | .t097 => bounds097
  | .t098 => bounds098
  | .t099 => bounds099
  | .t100 => bounds100
  | .t101 => bounds101
  | .t102 => bounds102
  | .t103 => bounds103
  | .t104 => bounds104
  | .t105 => bounds105
  | .t106 => bounds106
  | .t107 => bounds107
  | .t108 => bounds108
  | .t109 => bounds109
  | .t110 => bounds110
  | .t111 => bounds111
  | .t112 => bounds112
  | .t113 => bounds113
  | .t114 => bounds114
  | .t115 => bounds115
  | .t116 => bounds116
  | .t117 => bounds117
  | .t118 => bounds118
  | .t119 => bounds119
  | .t120 => bounds120
  | .t121 => bounds121
  | .t122 => bounds122
  | .t123 => bounds123
  | .t124 => bounds124
  | .t125 => bounds125
  | .t126 => bounds126
  | .t127 => bounds127
  | .t128 => bounds128
  | .t129 => bounds129
  | .t130 => bounds130
  | .t131 => bounds131
  | .t132 => bounds132
  | .t133 => bounds133
  | .t134 => bounds134
  | .t135 => bounds135
  | .t136 => bounds136
  | .t137 => bounds137
  | .t138 => bounds138
  | .t139 => bounds139
  | .t140 => bounds140
  | .t141 => bounds141
  | .t142 => bounds142
  | .t143 => bounds143
  | .t144 => bounds144
  | .t145 => bounds145
  | .t146 => bounds146
  | .t147 => bounds147
  | .t148 => bounds148
  | .t149 => bounds149
  | .t150 => bounds150
  | .t151 => bounds151
  | .t152 => bounds152
  | .t153 => bounds153
  | .t154 => bounds154
  | .t155 => bounds155
  | .t156 => bounds156
  | .t157 => bounds157
  | .t158 => bounds158
  | .t159 => bounds159
  | .t160 => bounds160
  | .t161 => bounds161
  | .t162 => bounds162
  | .t163 => bounds163
  | .t164 => bounds164
  | .t165 => bounds165
  | .t166 => bounds166
  | .t167 => bounds167
  | .t168 => bounds168
  | .t169 => bounds169
  | .t170 => bounds170
  | .t171 => bounds171
  | .t172 => bounds172
  | .t173 => bounds173
  | .t174 => bounds174
  | .t175 => bounds175
  | .t176 => bounds176
  | .t177 => bounds177
  | .t178 => bounds178
  | .t179 => bounds179
  | .t180 => bounds180
  | .t181 => bounds181
  | .t182 => bounds182
  | .t183 => bounds183
  | .t184 => bounds184
  | .t185 => bounds185
  | .t186 => bounds186
  | .t187 => bounds187
  | .t188 => bounds188
  | .t189 => bounds189
  | .t190 => bounds190
  | .t191 => bounds191
  | .t192 => bounds192
  | .t193 => bounds193
  | .t194 => bounds194
  | .t195 => bounds195
  | .t196 => bounds196
  | .t197 => bounds197
  | .t198 => bounds198
  | .t199 => bounds199
  | .t200 => bounds200
  | .t201 => bounds201
  | .t202 => bounds202
  | .t203 => bounds203
  | .t204 => bounds204
  | .t205 => bounds205
  | .t206 => bounds206
  | .t207 => bounds207
  | .t208 => bounds208
  | .t209 => bounds209
  | .t210 => bounds210
  | .t211 => bounds211
  | .t212 => bounds212
  | .t213 => bounds213
  | .t214 => bounds214
  | .t215 => bounds215
  | .t216 => bounds216
  | .t217 => bounds217
  | .t218 => bounds218
  | .t219 => bounds219
  | .t220 => bounds220
  | .t221 => bounds221
  | .t222 => bounds222
  | .t223 => bounds223
  | .t224 => bounds224
  | .t225 => bounds225
  | .t226 => bounds226
  | .t227 => bounds227
  | .t228 => bounds228
  | .t229 => bounds229
  | .t230 => bounds230
  | .t231 => bounds231
  | .t232 => bounds232
  | .t233 => bounds233
  | .t234 => bounds234
  | .t235 => bounds235
  | .t236 => bounds236
  | .t237 => bounds237
  | .t238 => bounds238
  | .t239 => bounds239
  | .t240 => bounds240
  | .t241 => bounds241
  | .t242 => bounds242
  | .t243 => bounds243
  | .t244 => bounds244
  | .t245 => bounds245
  | .t246 => bounds246
  | .t247 => bounds247
  | .t248 => bounds248
  | .t249 => bounds249
  | .t250 => bounds250
  | .t251 => bounds251
  | .t252 => bounds252
  | .t253 => bounds253
  | .t254 => bounds254
  | .t255 => bounds255
  | .t256 => bounds256
  | .t257 => bounds257
  | .t258 => bounds258
  | .t259 => bounds259
  | .t260 => bounds260
  | .t261 => bounds261
  | .t262 => bounds262
  | .t263 => bounds263
  | .t264 => bounds264
  | .t265 => bounds265
  | .t266 => bounds266
  | .t267 => bounds267
  | .t268 => bounds268
  | .t269 => bounds269
  | .t270 => bounds270
  | .t271 => bounds271
  | .t272 => bounds272
  | .t273 => bounds273
  | .t274 => bounds274
  | .t275 => bounds275
  | .t276 => bounds276
  | .t277 => bounds277
  | .t278 => bounds278
  | .t279 => bounds279
  | .t280 => bounds280
  | .t281 => bounds281
  | .t282 => bounds282
  | .t283 => bounds283
  | .t284 => bounds284
  | .t285 => bounds285
  | .t286 => bounds286
  | .t287 => bounds287
  | .t288 => bounds288
  | .t289 => bounds289
  | .t290 => bounds290
  | .t291 => bounds291
  | .t292 => bounds292
  | .t293 => bounds293
  | .t294 => bounds294
  | .t295 => bounds295
  | .t296 => bounds296
  | .t297 => bounds297
  | .t298 => bounds298
  | .t299 => bounds299
  | .t300 => bounds300
  | .t301 => bounds301
  | .t302 => bounds302
  | .t303 => bounds303
  | .t304 => bounds304
  | .t305 => bounds305
  | .t306 => bounds306
  | .t307 => bounds307
  | .t308 => bounds308
  | .t309 => bounds309
  | .t310 => bounds310
  | .t311 => bounds311
  | .t312 => bounds312
  | .t313 => bounds313
  | .t314 => bounds314
  | .t315 => bounds315
  | .t316 => bounds316
  | .t317 => bounds317
  | .t318 => bounds318
  | .t319 => bounds319
  | .t320 => bounds320
  | .t321 => bounds321
  | .t322 => bounds322
  | .t323 => bounds323
  | .t324 => bounds324
  | .t325 => bounds325
  | .t326 => bounds326
  | .t327 => bounds327
  | .t328 => bounds328
  | .t329 => bounds329
  | .t330 => bounds330
  | .t331 => bounds331
  | .t332 => bounds332
  | .t333 => bounds333
  | .t334 => bounds334
  | .t335 => bounds335
  | .t336 => bounds336
  | .t337 => bounds337
  | .t338 => bounds338
  | .t339 => bounds339
  | .t340 => bounds340
  | .t341 => bounds341
  | .t342 => bounds342
  | .t343 => bounds343
  | .t344 => bounds344
  | .t345 => bounds345
  | .t346 => bounds346
  | .t347 => bounds347
  | .t348 => bounds348
  | .t349 => bounds349
  | .t350 => bounds350
  | .t351 => bounds351
  | .t352 => bounds352
  | .t353 => bounds353
  | .t354 => bounds354
  | .t355 => bounds355
  | .t356 => bounds356
  | .t357 => bounds357
  | .t358 => bounds358
  | .t359 => bounds359
  | .t360 => bounds360
  | .t361 => bounds361
  | .t362 => bounds362
  | .t363 => bounds363
  | .t364 => bounds364
  | .t365 => bounds365
  | .t366 => bounds366
  | .t367 => bounds367
  | .t368 => bounds368
  | .t369 => bounds369
  | .t370 => bounds370
  | .t371 => bounds371
  | .t372 => bounds372
  | .t373 => bounds373
  | .t374 => bounds374
  | .t375 => bounds375
  | .t376 => bounds376
  | .t377 => bounds377
  | .t378 => bounds378
  | .t379 => bounds379
  | .t380 => bounds380
  | .t381 => bounds381
  | .t382 => bounds382
  | .t383 => bounds383
  | .t384 => bounds384
  | .t385 => bounds385
  | .t386 => bounds386
  | .t387 => bounds387
  | .t388 => bounds388
  | .t389 => bounds389
  | .t390 => bounds390
  | .t391 => bounds391
  | .t392 => bounds392
  | .t393 => bounds393
  | .t394 => bounds394
  | .t395 => bounds395
  | .t396 => bounds396
  | .t397 => bounds397
  | .t398 => bounds398
  | .t399 => bounds399
  | .t400 => bounds400
  | .t401 => bounds401
  | .t402 => bounds402
  | .t403 => bounds403
  | .t404 => bounds404
  | .t405 => bounds405
  | .t406 => bounds406
  | .t407 => bounds407
  | .t408 => bounds408
  | .t409 => bounds409
  | .t410 => bounds410
  | .t411 => bounds411
  | .t412 => bounds412
  | .t413 => bounds413
  | .t414 => bounds414
  | .t415 => bounds415
  | .t416 => bounds416
  | .t417 => bounds417
  | .t418 => bounds418
  | .t419 => bounds419
  | .t420 => bounds420
  | .t421 => bounds421
  | .t422 => bounds422
  | .t423 => bounds423
  | .t424 => bounds424
  | .t425 => bounds425
  | .t426 => bounds426
  | .t427 => bounds427
  | .t428 => bounds428
  | .t429 => bounds429
  | .t430 => bounds430
  | .t431 => bounds431
  | .t432 => bounds432
  | .t433 => bounds433
  | .t434 => bounds434
  | .t435 => bounds435
  | .t436 => bounds436
  | .t437 => bounds437
  | .t438 => bounds438
  | .t439 => bounds439
  | .t440 => bounds440
  | .t441 => bounds441
  | .t442 => bounds442
  | .t443 => bounds443
  | .t444 => bounds444
  | .t445 => bounds445
  | .t446 => bounds446
  | .t447 => bounds447
  | .t448 => bounds448
  | .t449 => bounds449
  | .t450 => bounds450
  | .t451 => bounds451
  | .t452 => bounds452
  | .t453 => bounds453
  | .t454 => bounds454
  | .t455 => bounds455
  | .t456 => bounds456
  | .t457 => bounds457
  | .t458 => bounds458
  | .t459 => bounds459
  | .t460 => bounds460
  | .t461 => bounds461
  | .t462 => bounds462
  | .t463 => bounds463
  | .t464 => bounds464
  | .t465 => bounds465
  | .t466 => bounds466
  | .t467 => bounds467
  | .t468 => bounds468
  | .t469 => bounds469
  | .t470 => bounds470
  | .t471 => bounds471
  | .t472 => bounds472
  | .t473 => bounds473
  | .t474 => bounds474
  | .t475 => bounds475
  | .t476 => bounds476
  | .t477 => bounds477
  | .t478 => bounds478
  | .t479 => bounds479
  | .t480 => bounds480
  | .t481 => bounds481
  | .t482 => bounds482
  | .t483 => bounds483
  | .t484 => bounds484
  | .t485 => bounds485
  | .t486 => bounds486
  | .t487 => bounds487
  | .t488 => bounds488
  | .t489 => bounds489
  | .t490 => bounds490
  | .t491 => bounds491
  | .t492 => bounds492
  | .t493 => bounds493
  | .t494 => bounds494
  | .t495 => bounds495
  | .t496 => bounds496
  | .t497 => bounds497
  | .t498 => bounds498
  | .t499 => bounds499
  | .t500 => bounds500
  | .t501 => bounds501
  | .t502 => bounds502
  | .t503 => bounds503
  | .t504 => bounds504
  | .t505 => bounds505
  | .t506 => bounds506
  | .t507 => bounds507
  | .t508 => bounds508
  | .t509 => bounds509
  | .t510 => bounds510
  | .t511 => bounds511
  | .t512 => bounds512
  | .t513 => bounds513
  | .t514 => bounds514
  | .t515 => bounds515
  | .t516 => bounds516
  | .t517 => bounds517
  | .t518 => bounds518
  | .t519 => bounds519
  | .t520 => bounds520
  | .t521 => bounds521
  | .t522 => bounds522
  | .t523 => bounds523
  | .t524 => bounds524
  | .t525 => bounds525
  | .t526 => bounds526
  | .t527 => bounds527
  | .t528 => bounds528
  | .t529 => bounds529
  | .t530 => bounds530
  | .t531 => bounds531
  | .t532 => bounds532
  | .t533 => bounds533
  | .t534 => bounds534
  | .t535 => bounds535
  | .t536 => bounds536
  | .t537 => bounds537
  | .t538 => bounds538
  | .t539 => bounds539
  | .t540 => bounds540
  | .t541 => bounds541
  | .t542 => bounds542
  | .t543 => bounds543
  | .t544 => bounds544
  | .t545 => bounds545
  | .t546 => bounds546
  | .t547 => bounds547
  | .t548 => bounds548
  | .t549 => bounds549
  | .t550 => bounds550
  | .t551 => bounds551
  | .t552 => bounds552
  | .t553 => bounds553
  | .t554 => bounds554
  | .t555 => bounds555
  | .t556 => bounds556
  | .t557 => bounds557
  | .t558 => bounds558
  | .t559 => bounds559
  | .t560 => bounds560
  | .t561 => bounds561
  | .t562 => bounds562
  | .t563 => bounds563
  | .t564 => bounds564
  | .t565 => bounds565
  | .t566 => bounds566
  | .t567 => bounds567
  | .t568 => bounds568
  | .t569 => bounds569
  | .t570 => bounds570
  | .t571 => bounds571
  | .t572 => bounds572
  | .t573 => bounds573
  | .t574 => bounds574
  | .t575 => bounds575
  | .t576 => bounds576
  | .t577 => bounds577
  | .t578 => bounds578
  | .t579 => bounds579
  | .t580 => bounds580
  | .t581 => bounds581
  | .t582 => bounds582
  | .t583 => bounds583
  | .t584 => bounds584
  | .t585 => bounds585
  | .t586 => bounds586
  | .t587 => bounds587
  | .t588 => bounds588
  | .t589 => bounds589
  | .t590 => bounds590
  | .t591 => bounds591
  | .t592 => bounds592
  | .t593 => bounds593
  | .t594 => bounds594
  | .t595 => bounds595
  | .t596 => bounds596
  | .t597 => bounds597
  | .t598 => bounds598
  | .t599 => bounds599
  | .t600 => bounds600
  | .t601 => bounds601
  | .t602 => bounds602
  | .t603 => bounds603
  | .t604 => bounds604
  | .t605 => bounds605
  | .t606 => bounds606
  | .t607 => bounds607
  | .t608 => bounds608
  | .t609 => bounds609
  | .t610 => bounds610
  | .t611 => bounds611
  | .t612 => bounds612
  | .t613 => bounds613
  | .t614 => bounds614
  | .t615 => bounds615
  | .t616 => bounds616
  | .t617 => bounds617
  | .t618 => bounds618
  | .t619 => bounds619
  | .t620 => bounds620
  | .t621 => bounds621
  | .t622 => bounds622
  | .t623 => bounds623
  | .t624 => bounds624
  | .t625 => bounds625
  | .t626 => bounds626
  | .t627 => bounds627
  | .t628 => bounds628
  | .t629 => bounds629
  | .t630 => bounds630
  | .t631 => bounds631
  | .t632 => bounds632
  | .t633 => bounds633
  | .t634 => bounds634
  | .t635 => bounds635
  | .t636 => bounds636
  | .t637 => bounds637
  | .t638 => bounds638
  | .t639 => bounds639
  | .t640 => bounds640
  | .t641 => bounds641
  | .t642 => bounds642
  | .t643 => bounds643
  | .t644 => bounds644
  | .t645 => bounds645
  | .t646 => bounds646
  | .t647 => bounds647
  | .t648 => bounds648
  | .t649 => bounds649
  | .t650 => bounds650
  | .t651 => bounds651
  | .t652 => bounds652
  | .t653 => bounds653
  | .t654 => bounds654
  | .t655 => bounds655
  | .t656 => bounds656
  | .t657 => bounds657
  | .t658 => bounds658
  | .t659 => bounds659
  | .t660 => bounds660
  | .t661 => bounds661
  | .t662 => bounds662
  | .t663 => bounds663
  | .t664 => bounds664
  | .t665 => bounds665
  | .t666 => bounds666
  | .t667 => bounds667
  | .t668 => bounds668
  | .t669 => bounds669
  | .t670 => bounds670
  | .t671 => bounds671
  | .t672 => bounds672
  | .t673 => bounds673
  | .t674 => bounds674
  | .t675 => bounds675
  | .t676 => bounds676
  | .t677 => bounds677
  | .t678 => bounds678
  | .t679 => bounds679
  | .t680 => bounds680
  | .t681 => bounds681
  | .t682 => bounds682
  | .t683 => bounds683
  | .t684 => bounds684
  | .t685 => bounds685
  | .t686 => bounds686
  | .t687 => bounds687
  | .t688 => bounds688
  | .t689 => bounds689
  | .t690 => bounds690
  | .t691 => bounds691
  | .t692 => bounds692
  | .t693 => bounds693
  | .t694 => bounds694
  | .t695 => bounds695
  | .t696 => bounds696
  | .t697 => bounds697
  | .t698 => bounds698
  | .t699 => bounds699
  | .t700 => bounds700
  | .t701 => bounds701
  | .t702 => bounds702
  | .t703 => bounds703
  | .t704 => bounds704
  | .t705 => bounds705
  | .t706 => bounds706
  | .t707 => bounds707
  | .t708 => bounds708
  | .t709 => bounds709
  | .t710 => bounds710
  | .t711 => bounds711
  | .t712 => bounds712
  | .t713 => bounds713
  | .t714 => bounds714
  | .t715 => bounds715
  | .t716 => bounds716
  | .t717 => bounds717
  | .t718 => bounds718
  | .t719 => bounds719
  | .t720 => bounds720
  | .t721 => bounds721
  | .t722 => bounds722
  | .t723 => bounds723
  | .t724 => bounds724
  | .t725 => bounds725
  | .t726 => bounds726
  | .t727 => bounds727
  | .t728 => bounds728
  | .t729 => bounds729
  | .t730 => bounds730
  | .t731 => bounds731
  | .t732 => bounds732
  | .t733 => bounds733
  | .t734 => bounds734
  | .t735 => bounds735
  | .t736 => bounds736
  | .t737 => bounds737
  | .t738 => bounds738
  | .t739 => bounds739
  | .t740 => bounds740
  | .t741 => bounds741
  | .t742 => bounds742
  | .t743 => bounds743
  | .t744 => bounds744
  | .t745 => bounds745
  | .t746 => bounds746
  | .t747 => bounds747
  | .t748 => bounds748
  | .t749 => bounds749
  | .t750 => bounds750
  | .t751 => bounds751
  | .t752 => bounds752
  | .t753 => bounds753
  | .t754 => bounds754
  | .t755 => bounds755
  | .t756 => bounds756
  | .t757 => bounds757
  | .t758 => bounds758
  | .t759 => bounds759
  | .t760 => bounds760
  | .t761 => bounds761
  | .t762 => bounds762
  | .t763 => bounds763
  | .t764 => bounds764
  | .t765 => bounds765
  | .t766 => bounds766
  | .t767 => bounds767
  | .t768 => bounds768
  | .t769 => bounds769
  | .t770 => bounds770
  | .t771 => bounds771
  | .t772 => bounds772
  | .t773 => bounds773
  | .t774 => bounds774
  | .t775 => bounds775
  | .t776 => bounds776
  | .t777 => bounds777
  | .t778 => bounds778
  | .t779 => bounds779
  | .t780 => bounds780
  | .t781 => bounds781
  | .t782 => bounds782
  | .t783 => bounds783
  | .t784 => bounds784
  | .t785 => bounds785
  | .t786 => bounds786
  | .t787 => bounds787
  | .t788 => bounds788
  | .t789 => bounds789
  | .t790 => bounds790
  | .t791 => bounds791
  | .t792 => bounds792
  | .t793 => bounds793
  | .t794 => bounds794
  | .t795 => bounds795
  | .t796 => bounds796
  | .t797 => bounds797
  | .t798 => bounds798
  | .t799 => bounds799
  | .t800 => bounds800
  | .t801 => bounds801
  | .t802 => bounds802
  | .t803 => bounds803
  | .t804 => bounds804
  | .t805 => bounds805
  | .t806 => bounds806

theorem all_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i))
    (k : TermIndex) : (coefficientInterval k).mem (gathered (exponents k) c a) :=
  AAATreeData.gathered_of_bounds c a hC ha k (bounds k)

/-- The existing full AAA H00 certificate now applies to the entire gathered
coefficient family. This still does not identify the actual residual. -/
theorem gathered_h00_mem (c : TermIndex → ℝ) (a x : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i))
    (hx : ∀ i, (relativeBox i).mem (x i)) :
    targetH00.mem
      (Interval.SparsePolynomial.axisDeriv
        (Interval.SparsePolynomial.axisDeriv
          (fun y => Interval.SparsePolynomial.eval exponents
            (fun k => gathered (exponents k) c a) y terms) 0) 0 x) :=
  actual_h00_mem (fun k => gathered (exponents k) c a) x (all_gathered c a hC ha) hx

theorem t001_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t001).mem (gathered (exponents .t001) c a) :=
  all_gathered c a hC ha .t001

theorem t002_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t002).mem (gathered (exponents .t002) c a) :=
  all_gathered c a hC ha .t002

theorem t003_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t003).mem (gathered (exponents .t003) c a) :=
  all_gathered c a hC ha .t003

theorem t004_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t004).mem (gathered (exponents .t004) c a) :=
  all_gathered c a hC ha .t004

theorem t005_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t005).mem (gathered (exponents .t005) c a) :=
  all_gathered c a hC ha .t005

theorem t006_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t006).mem (gathered (exponents .t006) c a) :=
  all_gathered c a hC ha .t006

theorem t007_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t007).mem (gathered (exponents .t007) c a) :=
  all_gathered c a hC ha .t007

theorem t008_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t008).mem (gathered (exponents .t008) c a) :=
  all_gathered c a hC ha .t008

theorem t009_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t009).mem (gathered (exponents .t009) c a) :=
  all_gathered c a hC ha .t009

theorem t010_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t010).mem (gathered (exponents .t010) c a) :=
  all_gathered c a hC ha .t010

theorem t028_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t028).mem (gathered (exponents .t028) c a) :=
  all_gathered c a hC ha .t028

theorem t029_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t029).mem (gathered (exponents .t029) c a) :=
  all_gathered c a hC ha .t029

theorem t030_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t030).mem (gathered (exponents .t030) c a) :=
  all_gathered c a hC ha .t030

theorem t031_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t031).mem (gathered (exponents .t031) c a) :=
  all_gathered c a hC ha .t031

theorem t032_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t032).mem (gathered (exponents .t032) c a) :=
  all_gathered c a hC ha .t032

theorem t033_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t033).mem (gathered (exponents .t033) c a) :=
  all_gathered c a hC ha .t033

theorem t034_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t034).mem (gathered (exponents .t034) c a) :=
  all_gathered c a hC ha .t034

theorem t035_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t035).mem (gathered (exponents .t035) c a) :=
  all_gathered c a hC ha .t035

theorem t036_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t036).mem (gathered (exponents .t036) c a) :=
  all_gathered c a hC ha .t036

theorem t037_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t037).mem (gathered (exponents .t037) c a) :=
  all_gathered c a hC ha .t037

theorem t039_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t039).mem (gathered (exponents .t039) c a) :=
  all_gathered c a hC ha .t039

theorem t040_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t040).mem (gathered (exponents .t040) c a) :=
  all_gathered c a hC ha .t040

theorem t041_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t041).mem (gathered (exponents .t041) c a) :=
  all_gathered c a hC ha .t041

theorem t042_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t042).mem (gathered (exponents .t042) c a) :=
  all_gathered c a hC ha .t042

theorem t043_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t043).mem (gathered (exponents .t043) c a) :=
  all_gathered c a hC ha .t043

theorem t044_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t044).mem (gathered (exponents .t044) c a) :=
  all_gathered c a hC ha .t044

theorem t045_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t045).mem (gathered (exponents .t045) c a) :=
  all_gathered c a hC ha .t045

theorem t046_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t046).mem (gathered (exponents .t046) c a) :=
  all_gathered c a hC ha .t046

theorem t047_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t047).mem (gathered (exponents .t047) c a) :=
  all_gathered c a hC ha .t047

theorem t048_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t048).mem (gathered (exponents .t048) c a) :=
  all_gathered c a hC ha .t048

theorem t050_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t050).mem (gathered (exponents .t050) c a) :=
  all_gathered c a hC ha .t050

theorem t051_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t051).mem (gathered (exponents .t051) c a) :=
  all_gathered c a hC ha .t051

theorem t052_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t052).mem (gathered (exponents .t052) c a) :=
  all_gathered c a hC ha .t052

theorem t053_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t053).mem (gathered (exponents .t053) c a) :=
  all_gathered c a hC ha .t053

theorem t054_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t054).mem (gathered (exponents .t054) c a) :=
  all_gathered c a hC ha .t054

theorem t055_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t055).mem (gathered (exponents .t055) c a) :=
  all_gathered c a hC ha .t055

theorem t056_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t056).mem (gathered (exponents .t056) c a) :=
  all_gathered c a hC ha .t056

theorem t057_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t057).mem (gathered (exponents .t057) c a) :=
  all_gathered c a hC ha .t057

theorem t058_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t058).mem (gathered (exponents .t058) c a) :=
  all_gathered c a hC ha .t058

theorem t059_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t059).mem (gathered (exponents .t059) c a) :=
  all_gathered c a hC ha .t059

theorem t061_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t061).mem (gathered (exponents .t061) c a) :=
  all_gathered c a hC ha .t061

theorem t062_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t062).mem (gathered (exponents .t062) c a) :=
  all_gathered c a hC ha .t062

theorem t063_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t063).mem (gathered (exponents .t063) c a) :=
  all_gathered c a hC ha .t063

theorem t064_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t064).mem (gathered (exponents .t064) c a) :=
  all_gathered c a hC ha .t064

theorem t065_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t065).mem (gathered (exponents .t065) c a) :=
  all_gathered c a hC ha .t065

theorem t066_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t066).mem (gathered (exponents .t066) c a) :=
  all_gathered c a hC ha .t066

theorem t067_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t067).mem (gathered (exponents .t067) c a) :=
  all_gathered c a hC ha .t067

theorem t068_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t068).mem (gathered (exponents .t068) c a) :=
  all_gathered c a hC ha .t068

theorem t069_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t069).mem (gathered (exponents .t069) c a) :=
  all_gathered c a hC ha .t069

theorem t070_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t070).mem (gathered (exponents .t070) c a) :=
  all_gathered c a hC ha .t070

theorem t072_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t072).mem (gathered (exponents .t072) c a) :=
  all_gathered c a hC ha .t072

theorem t073_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t073).mem (gathered (exponents .t073) c a) :=
  all_gathered c a hC ha .t073

theorem t074_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t074).mem (gathered (exponents .t074) c a) :=
  all_gathered c a hC ha .t074

theorem t075_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t075).mem (gathered (exponents .t075) c a) :=
  all_gathered c a hC ha .t075

theorem t076_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t076).mem (gathered (exponents .t076) c a) :=
  all_gathered c a hC ha .t076

theorem t077_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t077).mem (gathered (exponents .t077) c a) :=
  all_gathered c a hC ha .t077

theorem t078_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t078).mem (gathered (exponents .t078) c a) :=
  all_gathered c a hC ha .t078

theorem t079_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t079).mem (gathered (exponents .t079) c a) :=
  all_gathered c a hC ha .t079

theorem t080_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t080).mem (gathered (exponents .t080) c a) :=
  all_gathered c a hC ha .t080

theorem t081_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t081).mem (gathered (exponents .t081) c a) :=
  all_gathered c a hC ha .t081

theorem t083_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t083).mem (gathered (exponents .t083) c a) :=
  all_gathered c a hC ha .t083

theorem t084_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t084).mem (gathered (exponents .t084) c a) :=
  all_gathered c a hC ha .t084

theorem t085_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t085).mem (gathered (exponents .t085) c a) :=
  all_gathered c a hC ha .t085

theorem t086_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t086).mem (gathered (exponents .t086) c a) :=
  all_gathered c a hC ha .t086

theorem t087_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t087).mem (gathered (exponents .t087) c a) :=
  all_gathered c a hC ha .t087

theorem t088_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t088).mem (gathered (exponents .t088) c a) :=
  all_gathered c a hC ha .t088

theorem t089_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t089).mem (gathered (exponents .t089) c a) :=
  all_gathered c a hC ha .t089

theorem t090_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t090).mem (gathered (exponents .t090) c a) :=
  all_gathered c a hC ha .t090

theorem t091_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t091).mem (gathered (exponents .t091) c a) :=
  all_gathered c a hC ha .t091

theorem t092_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t092).mem (gathered (exponents .t092) c a) :=
  all_gathered c a hC ha .t092

theorem t094_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t094).mem (gathered (exponents .t094) c a) :=
  all_gathered c a hC ha .t094

theorem t095_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t095).mem (gathered (exponents .t095) c a) :=
  all_gathered c a hC ha .t095

theorem t096_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t096).mem (gathered (exponents .t096) c a) :=
  all_gathered c a hC ha .t096

theorem t097_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t097).mem (gathered (exponents .t097) c a) :=
  all_gathered c a hC ha .t097

theorem t098_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t098).mem (gathered (exponents .t098) c a) :=
  all_gathered c a hC ha .t098

theorem t099_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t099).mem (gathered (exponents .t099) c a) :=
  all_gathered c a hC ha .t099

theorem t100_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t100).mem (gathered (exponents .t100) c a) :=
  all_gathered c a hC ha .t100

theorem t101_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t101).mem (gathered (exponents .t101) c a) :=
  all_gathered c a hC ha .t101

theorem t102_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t102).mem (gathered (exponents .t102) c a) :=
  all_gathered c a hC ha .t102

theorem t105_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t105).mem (gathered (exponents .t105) c a) :=
  all_gathered c a hC ha .t105

theorem t106_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t106).mem (gathered (exponents .t106) c a) :=
  all_gathered c a hC ha .t106

theorem t107_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t107).mem (gathered (exponents .t107) c a) :=
  all_gathered c a hC ha .t107

theorem t108_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t108).mem (gathered (exponents .t108) c a) :=
  all_gathered c a hC ha .t108

theorem t109_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t109).mem (gathered (exponents .t109) c a) :=
  all_gathered c a hC ha .t109

theorem t110_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t110).mem (gathered (exponents .t110) c a) :=
  all_gathered c a hC ha .t110

theorem t111_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t111).mem (gathered (exponents .t111) c a) :=
  all_gathered c a hC ha .t111

theorem t112_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t112).mem (gathered (exponents .t112) c a) :=
  all_gathered c a hC ha .t112

theorem t113_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t113).mem (gathered (exponents .t113) c a) :=
  all_gathered c a hC ha .t113

theorem t116_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t116).mem (gathered (exponents .t116) c a) :=
  all_gathered c a hC ha .t116

theorem t117_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t117).mem (gathered (exponents .t117) c a) :=
  all_gathered c a hC ha .t117

theorem t118_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t118).mem (gathered (exponents .t118) c a) :=
  all_gathered c a hC ha .t118

theorem t119_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t119).mem (gathered (exponents .t119) c a) :=
  all_gathered c a hC ha .t119

theorem t120_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t120).mem (gathered (exponents .t120) c a) :=
  all_gathered c a hC ha .t120

theorem t121_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t121).mem (gathered (exponents .t121) c a) :=
  all_gathered c a hC ha .t121

theorem t122_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t122).mem (gathered (exponents .t122) c a) :=
  all_gathered c a hC ha .t122

theorem t127_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t127).mem (gathered (exponents .t127) c a) :=
  all_gathered c a hC ha .t127

theorem t155_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t155).mem (gathered (exponents .t155) c a) :=
  all_gathered c a hC ha .t155

theorem t156_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t156).mem (gathered (exponents .t156) c a) :=
  all_gathered c a hC ha .t156

theorem t157_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t157).mem (gathered (exponents .t157) c a) :=
  all_gathered c a hC ha .t157

theorem t158_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t158).mem (gathered (exponents .t158) c a) :=
  all_gathered c a hC ha .t158

theorem t159_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t159).mem (gathered (exponents .t159) c a) :=
  all_gathered c a hC ha .t159

theorem t160_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t160).mem (gathered (exponents .t160) c a) :=
  all_gathered c a hC ha .t160

theorem t161_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t161).mem (gathered (exponents .t161) c a) :=
  all_gathered c a hC ha .t161

theorem t162_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t162).mem (gathered (exponents .t162) c a) :=
  all_gathered c a hC ha .t162

theorem t163_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t163).mem (gathered (exponents .t163) c a) :=
  all_gathered c a hC ha .t163

theorem t164_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t164).mem (gathered (exponents .t164) c a) :=
  all_gathered c a hC ha .t164

theorem t166_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t166).mem (gathered (exponents .t166) c a) :=
  all_gathered c a hC ha .t166

theorem t167_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t167).mem (gathered (exponents .t167) c a) :=
  all_gathered c a hC ha .t167

theorem t168_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t168).mem (gathered (exponents .t168) c a) :=
  all_gathered c a hC ha .t168

theorem t169_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t169).mem (gathered (exponents .t169) c a) :=
  all_gathered c a hC ha .t169

theorem t170_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t170).mem (gathered (exponents .t170) c a) :=
  all_gathered c a hC ha .t170

theorem t171_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t171).mem (gathered (exponents .t171) c a) :=
  all_gathered c a hC ha .t171

theorem t172_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t172).mem (gathered (exponents .t172) c a) :=
  all_gathered c a hC ha .t172

theorem t173_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t173).mem (gathered (exponents .t173) c a) :=
  all_gathered c a hC ha .t173

theorem t174_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t174).mem (gathered (exponents .t174) c a) :=
  all_gathered c a hC ha .t174

theorem t175_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t175).mem (gathered (exponents .t175) c a) :=
  all_gathered c a hC ha .t175

theorem t176_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t176).mem (gathered (exponents .t176) c a) :=
  all_gathered c a hC ha .t176

theorem t177_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t177).mem (gathered (exponents .t177) c a) :=
  all_gathered c a hC ha .t177

theorem t178_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t178).mem (gathered (exponents .t178) c a) :=
  all_gathered c a hC ha .t178

theorem t179_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t179).mem (gathered (exponents .t179) c a) :=
  all_gathered c a hC ha .t179

theorem t180_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t180).mem (gathered (exponents .t180) c a) :=
  all_gathered c a hC ha .t180

theorem t181_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t181).mem (gathered (exponents .t181) c a) :=
  all_gathered c a hC ha .t181

theorem t182_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t182).mem (gathered (exponents .t182) c a) :=
  all_gathered c a hC ha .t182

theorem t183_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t183).mem (gathered (exponents .t183) c a) :=
  all_gathered c a hC ha .t183

theorem t184_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t184).mem (gathered (exponents .t184) c a) :=
  all_gathered c a hC ha .t184

theorem t186_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t186).mem (gathered (exponents .t186) c a) :=
  all_gathered c a hC ha .t186

theorem t187_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t187).mem (gathered (exponents .t187) c a) :=
  all_gathered c a hC ha .t187

theorem t188_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t188).mem (gathered (exponents .t188) c a) :=
  all_gathered c a hC ha .t188

theorem t189_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t189).mem (gathered (exponents .t189) c a) :=
  all_gathered c a hC ha .t189

theorem t190_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t190).mem (gathered (exponents .t190) c a) :=
  all_gathered c a hC ha .t190

theorem t191_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t191).mem (gathered (exponents .t191) c a) :=
  all_gathered c a hC ha .t191

theorem t192_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t192).mem (gathered (exponents .t192) c a) :=
  all_gathered c a hC ha .t192

theorem t193_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t193).mem (gathered (exponents .t193) c a) :=
  all_gathered c a hC ha .t193

theorem t194_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t194).mem (gathered (exponents .t194) c a) :=
  all_gathered c a hC ha .t194

theorem t196_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t196).mem (gathered (exponents .t196) c a) :=
  all_gathered c a hC ha .t196

theorem t197_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t197).mem (gathered (exponents .t197) c a) :=
  all_gathered c a hC ha .t197

theorem t198_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t198).mem (gathered (exponents .t198) c a) :=
  all_gathered c a hC ha .t198

theorem t199_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t199).mem (gathered (exponents .t199) c a) :=
  all_gathered c a hC ha .t199

theorem t200_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t200).mem (gathered (exponents .t200) c a) :=
  all_gathered c a hC ha .t200

theorem t201_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t201).mem (gathered (exponents .t201) c a) :=
  all_gathered c a hC ha .t201

theorem t202_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t202).mem (gathered (exponents .t202) c a) :=
  all_gathered c a hC ha .t202

theorem t203_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t203).mem (gathered (exponents .t203) c a) :=
  all_gathered c a hC ha .t203

theorem t204_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t204).mem (gathered (exponents .t204) c a) :=
  all_gathered c a hC ha .t204

theorem t206_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t206).mem (gathered (exponents .t206) c a) :=
  all_gathered c a hC ha .t206

theorem t207_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t207).mem (gathered (exponents .t207) c a) :=
  all_gathered c a hC ha .t207

theorem t208_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t208).mem (gathered (exponents .t208) c a) :=
  all_gathered c a hC ha .t208

theorem t209_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t209).mem (gathered (exponents .t209) c a) :=
  all_gathered c a hC ha .t209

theorem t210_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t210).mem (gathered (exponents .t210) c a) :=
  all_gathered c a hC ha .t210

theorem t211_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t211).mem (gathered (exponents .t211) c a) :=
  all_gathered c a hC ha .t211

theorem t212_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t212).mem (gathered (exponents .t212) c a) :=
  all_gathered c a hC ha .t212

theorem t213_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t213).mem (gathered (exponents .t213) c a) :=
  all_gathered c a hC ha .t213

theorem t214_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t214).mem (gathered (exponents .t214) c a) :=
  all_gathered c a hC ha .t214

theorem t216_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t216).mem (gathered (exponents .t216) c a) :=
  all_gathered c a hC ha .t216

theorem t217_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t217).mem (gathered (exponents .t217) c a) :=
  all_gathered c a hC ha .t217

theorem t218_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t218).mem (gathered (exponents .t218) c a) :=
  all_gathered c a hC ha .t218

theorem t219_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t219).mem (gathered (exponents .t219) c a) :=
  all_gathered c a hC ha .t219

theorem t220_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t220).mem (gathered (exponents .t220) c a) :=
  all_gathered c a hC ha .t220

theorem t221_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t221).mem (gathered (exponents .t221) c a) :=
  all_gathered c a hC ha .t221

theorem t222_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t222).mem (gathered (exponents .t222) c a) :=
  all_gathered c a hC ha .t222

theorem t223_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t223).mem (gathered (exponents .t223) c a) :=
  all_gathered c a hC ha .t223

theorem t226_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t226).mem (gathered (exponents .t226) c a) :=
  all_gathered c a hC ha .t226

theorem t227_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t227).mem (gathered (exponents .t227) c a) :=
  all_gathered c a hC ha .t227

theorem t228_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t228).mem (gathered (exponents .t228) c a) :=
  all_gathered c a hC ha .t228

theorem t229_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t229).mem (gathered (exponents .t229) c a) :=
  all_gathered c a hC ha .t229

theorem t230_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t230).mem (gathered (exponents .t230) c a) :=
  all_gathered c a hC ha .t230

theorem t231_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t231).mem (gathered (exponents .t231) c a) :=
  all_gathered c a hC ha .t231

theorem t232_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t232).mem (gathered (exponents .t232) c a) :=
  all_gathered c a hC ha .t232

theorem t233_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t233).mem (gathered (exponents .t233) c a) :=
  all_gathered c a hC ha .t233

theorem t236_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t236).mem (gathered (exponents .t236) c a) :=
  all_gathered c a hC ha .t236

theorem t237_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t237).mem (gathered (exponents .t237) c a) :=
  all_gathered c a hC ha .t237

theorem t238_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t238).mem (gathered (exponents .t238) c a) :=
  all_gathered c a hC ha .t238

theorem t239_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t239).mem (gathered (exponents .t239) c a) :=
  all_gathered c a hC ha .t239

theorem t240_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t240).mem (gathered (exponents .t240) c a) :=
  all_gathered c a hC ha .t240

theorem t241_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t241).mem (gathered (exponents .t241) c a) :=
  all_gathered c a hC ha .t241

theorem t246_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t246).mem (gathered (exponents .t246) c a) :=
  all_gathered c a hC ha .t246

theorem t247_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t247).mem (gathered (exponents .t247) c a) :=
  all_gathered c a hC ha .t247

theorem t257_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t257).mem (gathered (exponents .t257) c a) :=
  all_gathered c a hC ha .t257

theorem t258_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t258).mem (gathered (exponents .t258) c a) :=
  all_gathered c a hC ha .t258

theorem t259_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t259).mem (gathered (exponents .t259) c a) :=
  all_gathered c a hC ha .t259

theorem t260_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t260).mem (gathered (exponents .t260) c a) :=
  all_gathered c a hC ha .t260

theorem t261_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t261).mem (gathered (exponents .t261) c a) :=
  all_gathered c a hC ha .t261

theorem t262_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t262).mem (gathered (exponents .t262) c a) :=
  all_gathered c a hC ha .t262

theorem t263_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t263).mem (gathered (exponents .t263) c a) :=
  all_gathered c a hC ha .t263

theorem t264_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t264).mem (gathered (exponents .t264) c a) :=
  all_gathered c a hC ha .t264

theorem t265_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t265).mem (gathered (exponents .t265) c a) :=
  all_gathered c a hC ha .t265

theorem t266_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t266).mem (gathered (exponents .t266) c a) :=
  all_gathered c a hC ha .t266

theorem t268_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t268).mem (gathered (exponents .t268) c a) :=
  all_gathered c a hC ha .t268

theorem t269_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t269).mem (gathered (exponents .t269) c a) :=
  all_gathered c a hC ha .t269

theorem t270_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t270).mem (gathered (exponents .t270) c a) :=
  all_gathered c a hC ha .t270

theorem t271_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t271).mem (gathered (exponents .t271) c a) :=
  all_gathered c a hC ha .t271

theorem t272_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t272).mem (gathered (exponents .t272) c a) :=
  all_gathered c a hC ha .t272

theorem t273_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t273).mem (gathered (exponents .t273) c a) :=
  all_gathered c a hC ha .t273

theorem t274_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t274).mem (gathered (exponents .t274) c a) :=
  all_gathered c a hC ha .t274

theorem t275_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t275).mem (gathered (exponents .t275) c a) :=
  all_gathered c a hC ha .t275

theorem t276_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t276).mem (gathered (exponents .t276) c a) :=
  all_gathered c a hC ha .t276

theorem t278_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t278).mem (gathered (exponents .t278) c a) :=
  all_gathered c a hC ha .t278

theorem t279_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t279).mem (gathered (exponents .t279) c a) :=
  all_gathered c a hC ha .t279

theorem t280_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t280).mem (gathered (exponents .t280) c a) :=
  all_gathered c a hC ha .t280

theorem t281_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t281).mem (gathered (exponents .t281) c a) :=
  all_gathered c a hC ha .t281

theorem t282_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t282).mem (gathered (exponents .t282) c a) :=
  all_gathered c a hC ha .t282

theorem t283_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t283).mem (gathered (exponents .t283) c a) :=
  all_gathered c a hC ha .t283

theorem t284_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t284).mem (gathered (exponents .t284) c a) :=
  all_gathered c a hC ha .t284

theorem t285_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t285).mem (gathered (exponents .t285) c a) :=
  all_gathered c a hC ha .t285

theorem t287_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t287).mem (gathered (exponents .t287) c a) :=
  all_gathered c a hC ha .t287

theorem t288_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t288).mem (gathered (exponents .t288) c a) :=
  all_gathered c a hC ha .t288

theorem t289_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t289).mem (gathered (exponents .t289) c a) :=
  all_gathered c a hC ha .t289

theorem t290_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t290).mem (gathered (exponents .t290) c a) :=
  all_gathered c a hC ha .t290

theorem t291_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t291).mem (gathered (exponents .t291) c a) :=
  all_gathered c a hC ha .t291

theorem t292_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t292).mem (gathered (exponents .t292) c a) :=
  all_gathered c a hC ha .t292

theorem t293_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t293).mem (gathered (exponents .t293) c a) :=
  all_gathered c a hC ha .t293

theorem t294_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t294).mem (gathered (exponents .t294) c a) :=
  all_gathered c a hC ha .t294

theorem t296_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t296).mem (gathered (exponents .t296) c a) :=
  all_gathered c a hC ha .t296

theorem t297_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t297).mem (gathered (exponents .t297) c a) :=
  all_gathered c a hC ha .t297

theorem t298_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t298).mem (gathered (exponents .t298) c a) :=
  all_gathered c a hC ha .t298

theorem t299_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t299).mem (gathered (exponents .t299) c a) :=
  all_gathered c a hC ha .t299

theorem t300_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t300).mem (gathered (exponents .t300) c a) :=
  all_gathered c a hC ha .t300

theorem t301_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t301).mem (gathered (exponents .t301) c a) :=
  all_gathered c a hC ha .t301

theorem t302_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t302).mem (gathered (exponents .t302) c a) :=
  all_gathered c a hC ha .t302

theorem t303_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t303).mem (gathered (exponents .t303) c a) :=
  all_gathered c a hC ha .t303

theorem t305_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t305).mem (gathered (exponents .t305) c a) :=
  all_gathered c a hC ha .t305

theorem t306_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t306).mem (gathered (exponents .t306) c a) :=
  all_gathered c a hC ha .t306

theorem t307_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t307).mem (gathered (exponents .t307) c a) :=
  all_gathered c a hC ha .t307

theorem t308_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t308).mem (gathered (exponents .t308) c a) :=
  all_gathered c a hC ha .t308

theorem t309_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t309).mem (gathered (exponents .t309) c a) :=
  all_gathered c a hC ha .t309

theorem t310_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t310).mem (gathered (exponents .t310) c a) :=
  all_gathered c a hC ha .t310

theorem t311_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t311).mem (gathered (exponents .t311) c a) :=
  all_gathered c a hC ha .t311

theorem t314_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t314).mem (gathered (exponents .t314) c a) :=
  all_gathered c a hC ha .t314

theorem t315_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t315).mem (gathered (exponents .t315) c a) :=
  all_gathered c a hC ha .t315

theorem t316_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t316).mem (gathered (exponents .t316) c a) :=
  all_gathered c a hC ha .t316

theorem t317_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t317).mem (gathered (exponents .t317) c a) :=
  all_gathered c a hC ha .t317

theorem t318_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t318).mem (gathered (exponents .t318) c a) :=
  all_gathered c a hC ha .t318

theorem t319_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t319).mem (gathered (exponents .t319) c a) :=
  all_gathered c a hC ha .t319

theorem t320_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t320).mem (gathered (exponents .t320) c a) :=
  all_gathered c a hC ha .t320

theorem t323_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t323).mem (gathered (exponents .t323) c a) :=
  all_gathered c a hC ha .t323

theorem t324_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t324).mem (gathered (exponents .t324) c a) :=
  all_gathered c a hC ha .t324

theorem t325_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t325).mem (gathered (exponents .t325) c a) :=
  all_gathered c a hC ha .t325

theorem t326_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t326).mem (gathered (exponents .t326) c a) :=
  all_gathered c a hC ha .t326

theorem t327_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t327).mem (gathered (exponents .t327) c a) :=
  all_gathered c a hC ha .t327

theorem t332_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t332).mem (gathered (exponents .t332) c a) :=
  all_gathered c a hC ha .t332

theorem t333_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t333).mem (gathered (exponents .t333) c a) :=
  all_gathered c a hC ha .t333

theorem t341_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t341).mem (gathered (exponents .t341) c a) :=
  all_gathered c a hC ha .t341

theorem t344_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t344).mem (gathered (exponents .t344) c a) :=
  all_gathered c a hC ha .t344

theorem t345_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t345).mem (gathered (exponents .t345) c a) :=
  all_gathered c a hC ha .t345

theorem t346_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t346).mem (gathered (exponents .t346) c a) :=
  all_gathered c a hC ha .t346

theorem t347_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t347).mem (gathered (exponents .t347) c a) :=
  all_gathered c a hC ha .t347

theorem t348_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t348).mem (gathered (exponents .t348) c a) :=
  all_gathered c a hC ha .t348

theorem t349_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t349).mem (gathered (exponents .t349) c a) :=
  all_gathered c a hC ha .t349

theorem t350_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t350).mem (gathered (exponents .t350) c a) :=
  all_gathered c a hC ha .t350

theorem t351_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t351).mem (gathered (exponents .t351) c a) :=
  all_gathered c a hC ha .t351

theorem t352_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t352).mem (gathered (exponents .t352) c a) :=
  all_gathered c a hC ha .t352

theorem t353_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t353).mem (gathered (exponents .t353) c a) :=
  all_gathered c a hC ha .t353

theorem t355_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t355).mem (gathered (exponents .t355) c a) :=
  all_gathered c a hC ha .t355

theorem t356_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t356).mem (gathered (exponents .t356) c a) :=
  all_gathered c a hC ha .t356

theorem t357_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t357).mem (gathered (exponents .t357) c a) :=
  all_gathered c a hC ha .t357

theorem t358_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t358).mem (gathered (exponents .t358) c a) :=
  all_gathered c a hC ha .t358

theorem t359_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t359).mem (gathered (exponents .t359) c a) :=
  all_gathered c a hC ha .t359

theorem t360_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t360).mem (gathered (exponents .t360) c a) :=
  all_gathered c a hC ha .t360

theorem t361_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t361).mem (gathered (exponents .t361) c a) :=
  all_gathered c a hC ha .t361

theorem t362_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t362).mem (gathered (exponents .t362) c a) :=
  all_gathered c a hC ha .t362

theorem t363_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t363).mem (gathered (exponents .t363) c a) :=
  all_gathered c a hC ha .t363

theorem t365_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t365).mem (gathered (exponents .t365) c a) :=
  all_gathered c a hC ha .t365

theorem t366_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t366).mem (gathered (exponents .t366) c a) :=
  all_gathered c a hC ha .t366

theorem t367_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t367).mem (gathered (exponents .t367) c a) :=
  all_gathered c a hC ha .t367

theorem t368_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t368).mem (gathered (exponents .t368) c a) :=
  all_gathered c a hC ha .t368

theorem t369_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t369).mem (gathered (exponents .t369) c a) :=
  all_gathered c a hC ha .t369

theorem t370_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t370).mem (gathered (exponents .t370) c a) :=
  all_gathered c a hC ha .t370

theorem t371_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t371).mem (gathered (exponents .t371) c a) :=
  all_gathered c a hC ha .t371

theorem t372_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t372).mem (gathered (exponents .t372) c a) :=
  all_gathered c a hC ha .t372

theorem t374_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t374).mem (gathered (exponents .t374) c a) :=
  all_gathered c a hC ha .t374

theorem t375_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t375).mem (gathered (exponents .t375) c a) :=
  all_gathered c a hC ha .t375

theorem t376_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t376).mem (gathered (exponents .t376) c a) :=
  all_gathered c a hC ha .t376

theorem t377_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t377).mem (gathered (exponents .t377) c a) :=
  all_gathered c a hC ha .t377

theorem t378_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t378).mem (gathered (exponents .t378) c a) :=
  all_gathered c a hC ha .t378

theorem t379_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t379).mem (gathered (exponents .t379) c a) :=
  all_gathered c a hC ha .t379

theorem t380_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t380).mem (gathered (exponents .t380) c a) :=
  all_gathered c a hC ha .t380

theorem t382_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t382).mem (gathered (exponents .t382) c a) :=
  all_gathered c a hC ha .t382

theorem t383_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t383).mem (gathered (exponents .t383) c a) :=
  all_gathered c a hC ha .t383

theorem t384_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t384).mem (gathered (exponents .t384) c a) :=
  all_gathered c a hC ha .t384

theorem t385_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t385).mem (gathered (exponents .t385) c a) :=
  all_gathered c a hC ha .t385

theorem t386_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t386).mem (gathered (exponents .t386) c a) :=
  all_gathered c a hC ha .t386

theorem t387_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t387).mem (gathered (exponents .t387) c a) :=
  all_gathered c a hC ha .t387

theorem t390_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t390).mem (gathered (exponents .t390) c a) :=
  all_gathered c a hC ha .t390

theorem t391_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t391).mem (gathered (exponents .t391) c a) :=
  all_gathered c a hC ha .t391

theorem t392_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t392).mem (gathered (exponents .t392) c a) :=
  all_gathered c a hC ha .t392

theorem t393_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t393).mem (gathered (exponents .t393) c a) :=
  all_gathered c a hC ha .t393

theorem t394_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t394).mem (gathered (exponents .t394) c a) :=
  all_gathered c a hC ha .t394

theorem t395_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t395).mem (gathered (exponents .t395) c a) :=
  all_gathered c a hC ha .t395

theorem t398_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t398).mem (gathered (exponents .t398) c a) :=
  all_gathered c a hC ha .t398

theorem t399_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t399).mem (gathered (exponents .t399) c a) :=
  all_gathered c a hC ha .t399

theorem t400_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t400).mem (gathered (exponents .t400) c a) :=
  all_gathered c a hC ha .t400

theorem t401_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t401).mem (gathered (exponents .t401) c a) :=
  all_gathered c a hC ha .t401

theorem t406_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t406).mem (gathered (exponents .t406) c a) :=
  all_gathered c a hC ha .t406

theorem t407_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t407).mem (gathered (exponents .t407) c a) :=
  all_gathered c a hC ha .t407

theorem t408_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t408).mem (gathered (exponents .t408) c a) :=
  all_gathered c a hC ha .t408

theorem t414_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t414).mem (gathered (exponents .t414) c a) :=
  all_gathered c a hC ha .t414

theorem t415_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t415).mem (gathered (exponents .t415) c a) :=
  all_gathered c a hC ha .t415

theorem t417_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t417).mem (gathered (exponents .t417) c a) :=
  all_gathered c a hC ha .t417

theorem t420_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t420).mem (gathered (exponents .t420) c a) :=
  all_gathered c a hC ha .t420

theorem t421_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t421).mem (gathered (exponents .t421) c a) :=
  all_gathered c a hC ha .t421

theorem t422_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t422).mem (gathered (exponents .t422) c a) :=
  all_gathered c a hC ha .t422

theorem t423_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t423).mem (gathered (exponents .t423) c a) :=
  all_gathered c a hC ha .t423

theorem t424_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t424).mem (gathered (exponents .t424) c a) :=
  all_gathered c a hC ha .t424

theorem t425_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t425).mem (gathered (exponents .t425) c a) :=
  all_gathered c a hC ha .t425

theorem t426_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t426).mem (gathered (exponents .t426) c a) :=
  all_gathered c a hC ha .t426

theorem t427_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t427).mem (gathered (exponents .t427) c a) :=
  all_gathered c a hC ha .t427

theorem t428_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t428).mem (gathered (exponents .t428) c a) :=
  all_gathered c a hC ha .t428

theorem t429_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t429).mem (gathered (exponents .t429) c a) :=
  all_gathered c a hC ha .t429

theorem t431_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t431).mem (gathered (exponents .t431) c a) :=
  all_gathered c a hC ha .t431

theorem t432_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t432).mem (gathered (exponents .t432) c a) :=
  all_gathered c a hC ha .t432

theorem t433_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t433).mem (gathered (exponents .t433) c a) :=
  all_gathered c a hC ha .t433

theorem t434_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t434).mem (gathered (exponents .t434) c a) :=
  all_gathered c a hC ha .t434

theorem t435_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t435).mem (gathered (exponents .t435) c a) :=
  all_gathered c a hC ha .t435

theorem t436_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t436).mem (gathered (exponents .t436) c a) :=
  all_gathered c a hC ha .t436

theorem t437_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t437).mem (gathered (exponents .t437) c a) :=
  all_gathered c a hC ha .t437

theorem t438_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t438).mem (gathered (exponents .t438) c a) :=
  all_gathered c a hC ha .t438

theorem t439_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t439).mem (gathered (exponents .t439) c a) :=
  all_gathered c a hC ha .t439

theorem t441_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t441).mem (gathered (exponents .t441) c a) :=
  all_gathered c a hC ha .t441

theorem t442_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t442).mem (gathered (exponents .t442) c a) :=
  all_gathered c a hC ha .t442

theorem t443_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t443).mem (gathered (exponents .t443) c a) :=
  all_gathered c a hC ha .t443

theorem t444_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t444).mem (gathered (exponents .t444) c a) :=
  all_gathered c a hC ha .t444

theorem t445_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t445).mem (gathered (exponents .t445) c a) :=
  all_gathered c a hC ha .t445

theorem t446_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t446).mem (gathered (exponents .t446) c a) :=
  all_gathered c a hC ha .t446

theorem t447_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t447).mem (gathered (exponents .t447) c a) :=
  all_gathered c a hC ha .t447

theorem t448_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t448).mem (gathered (exponents .t448) c a) :=
  all_gathered c a hC ha .t448

theorem t450_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t450).mem (gathered (exponents .t450) c a) :=
  all_gathered c a hC ha .t450

theorem t451_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t451).mem (gathered (exponents .t451) c a) :=
  all_gathered c a hC ha .t451

theorem t452_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t452).mem (gathered (exponents .t452) c a) :=
  all_gathered c a hC ha .t452

theorem t453_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t453).mem (gathered (exponents .t453) c a) :=
  all_gathered c a hC ha .t453

theorem t454_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t454).mem (gathered (exponents .t454) c a) :=
  all_gathered c a hC ha .t454

theorem t455_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t455).mem (gathered (exponents .t455) c a) :=
  all_gathered c a hC ha .t455

theorem t458_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t458).mem (gathered (exponents .t458) c a) :=
  all_gathered c a hC ha .t458

theorem t459_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t459).mem (gathered (exponents .t459) c a) :=
  all_gathered c a hC ha .t459

theorem t460_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t460).mem (gathered (exponents .t460) c a) :=
  all_gathered c a hC ha .t460

theorem t461_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t461).mem (gathered (exponents .t461) c a) :=
  all_gathered c a hC ha .t461

theorem t462_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t462).mem (gathered (exponents .t462) c a) :=
  all_gathered c a hC ha .t462

theorem t465_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t465).mem (gathered (exponents .t465) c a) :=
  all_gathered c a hC ha .t465

theorem t466_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t466).mem (gathered (exponents .t466) c a) :=
  all_gathered c a hC ha .t466

theorem t467_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t467).mem (gathered (exponents .t467) c a) :=
  all_gathered c a hC ha .t467

theorem t468_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t468).mem (gathered (exponents .t468) c a) :=
  all_gathered c a hC ha .t468

theorem t472_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t472).mem (gathered (exponents .t472) c a) :=
  all_gathered c a hC ha .t472

theorem t473_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t473).mem (gathered (exponents .t473) c a) :=
  all_gathered c a hC ha .t473

theorem t474_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t474).mem (gathered (exponents .t474) c a) :=
  all_gathered c a hC ha .t474

theorem t479_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t479).mem (gathered (exponents .t479) c a) :=
  all_gathered c a hC ha .t479

theorem t480_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t480).mem (gathered (exponents .t480) c a) :=
  all_gathered c a hC ha .t480

theorem t481_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t481).mem (gathered (exponents .t481) c a) :=
  all_gathered c a hC ha .t481

theorem t483_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t483).mem (gathered (exponents .t483) c a) :=
  all_gathered c a hC ha .t483

theorem t484_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t484).mem (gathered (exponents .t484) c a) :=
  all_gathered c a hC ha .t484

theorem t486_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t486).mem (gathered (exponents .t486) c a) :=
  all_gathered c a hC ha .t486

theorem t489_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t489).mem (gathered (exponents .t489) c a) :=
  all_gathered c a hC ha .t489

theorem t490_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t490).mem (gathered (exponents .t490) c a) :=
  all_gathered c a hC ha .t490

theorem t491_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t491).mem (gathered (exponents .t491) c a) :=
  all_gathered c a hC ha .t491

theorem t492_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t492).mem (gathered (exponents .t492) c a) :=
  all_gathered c a hC ha .t492

theorem t493_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t493).mem (gathered (exponents .t493) c a) :=
  all_gathered c a hC ha .t493

theorem t494_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t494).mem (gathered (exponents .t494) c a) :=
  all_gathered c a hC ha .t494

theorem t495_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t495).mem (gathered (exponents .t495) c a) :=
  all_gathered c a hC ha .t495

theorem t496_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t496).mem (gathered (exponents .t496) c a) :=
  all_gathered c a hC ha .t496

theorem t497_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t497).mem (gathered (exponents .t497) c a) :=
  all_gathered c a hC ha .t497

theorem t498_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t498).mem (gathered (exponents .t498) c a) :=
  all_gathered c a hC ha .t498

theorem t500_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t500).mem (gathered (exponents .t500) c a) :=
  all_gathered c a hC ha .t500

theorem t501_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t501).mem (gathered (exponents .t501) c a) :=
  all_gathered c a hC ha .t501

theorem t502_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t502).mem (gathered (exponents .t502) c a) :=
  all_gathered c a hC ha .t502

theorem t503_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t503).mem (gathered (exponents .t503) c a) :=
  all_gathered c a hC ha .t503

theorem t504_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t504).mem (gathered (exponents .t504) c a) :=
  all_gathered c a hC ha .t504

theorem t505_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t505).mem (gathered (exponents .t505) c a) :=
  all_gathered c a hC ha .t505

theorem t506_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t506).mem (gathered (exponents .t506) c a) :=
  all_gathered c a hC ha .t506

theorem t507_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t507).mem (gathered (exponents .t507) c a) :=
  all_gathered c a hC ha .t507

theorem t508_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t508).mem (gathered (exponents .t508) c a) :=
  all_gathered c a hC ha .t508

theorem t510_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t510).mem (gathered (exponents .t510) c a) :=
  all_gathered c a hC ha .t510

theorem t511_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t511).mem (gathered (exponents .t511) c a) :=
  all_gathered c a hC ha .t511

theorem t512_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t512).mem (gathered (exponents .t512) c a) :=
  all_gathered c a hC ha .t512

theorem t513_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t513).mem (gathered (exponents .t513) c a) :=
  all_gathered c a hC ha .t513

theorem t514_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t514).mem (gathered (exponents .t514) c a) :=
  all_gathered c a hC ha .t514

theorem t515_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t515).mem (gathered (exponents .t515) c a) :=
  all_gathered c a hC ha .t515

theorem t516_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t516).mem (gathered (exponents .t516) c a) :=
  all_gathered c a hC ha .t516

theorem t519_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t519).mem (gathered (exponents .t519) c a) :=
  all_gathered c a hC ha .t519

theorem t520_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t520).mem (gathered (exponents .t520) c a) :=
  all_gathered c a hC ha .t520

theorem t521_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t521).mem (gathered (exponents .t521) c a) :=
  all_gathered c a hC ha .t521

theorem t522_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t522).mem (gathered (exponents .t522) c a) :=
  all_gathered c a hC ha .t522

theorem t523_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t523).mem (gathered (exponents .t523) c a) :=
  all_gathered c a hC ha .t523

theorem t524_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t524).mem (gathered (exponents .t524) c a) :=
  all_gathered c a hC ha .t524

theorem t527_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t527).mem (gathered (exponents .t527) c a) :=
  all_gathered c a hC ha .t527

theorem t528_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t528).mem (gathered (exponents .t528) c a) :=
  all_gathered c a hC ha .t528

theorem t529_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t529).mem (gathered (exponents .t529) c a) :=
  all_gathered c a hC ha .t529

theorem t530_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t530).mem (gathered (exponents .t530) c a) :=
  all_gathered c a hC ha .t530

theorem t534_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t534).mem (gathered (exponents .t534) c a) :=
  all_gathered c a hC ha .t534

theorem t535_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t535).mem (gathered (exponents .t535) c a) :=
  all_gathered c a hC ha .t535

theorem t536_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t536).mem (gathered (exponents .t536) c a) :=
  all_gathered c a hC ha .t536

theorem t537_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t537).mem (gathered (exponents .t537) c a) :=
  all_gathered c a hC ha .t537

theorem t540_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t540).mem (gathered (exponents .t540) c a) :=
  all_gathered c a hC ha .t540

theorem t541_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t541).mem (gathered (exponents .t541) c a) :=
  all_gathered c a hC ha .t541

theorem t542_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t542).mem (gathered (exponents .t542) c a) :=
  all_gathered c a hC ha .t542

theorem t545_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t545).mem (gathered (exponents .t545) c a) :=
  all_gathered c a hC ha .t545

theorem t546_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t546).mem (gathered (exponents .t546) c a) :=
  all_gathered c a hC ha .t546

theorem t549_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t549).mem (gathered (exponents .t549) c a) :=
  all_gathered c a hC ha .t549

theorem t550_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t550).mem (gathered (exponents .t550) c a) :=
  all_gathered c a hC ha .t550

theorem t552_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t552).mem (gathered (exponents .t552) c a) :=
  all_gathered c a hC ha .t552

theorem t555_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t555).mem (gathered (exponents .t555) c a) :=
  all_gathered c a hC ha .t555

theorem t556_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t556).mem (gathered (exponents .t556) c a) :=
  all_gathered c a hC ha .t556

theorem t557_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t557).mem (gathered (exponents .t557) c a) :=
  all_gathered c a hC ha .t557

theorem t558_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t558).mem (gathered (exponents .t558) c a) :=
  all_gathered c a hC ha .t558

theorem t559_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t559).mem (gathered (exponents .t559) c a) :=
  all_gathered c a hC ha .t559

theorem t560_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t560).mem (gathered (exponents .t560) c a) :=
  all_gathered c a hC ha .t560

theorem t561_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t561).mem (gathered (exponents .t561) c a) :=
  all_gathered c a hC ha .t561

theorem t562_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t562).mem (gathered (exponents .t562) c a) :=
  all_gathered c a hC ha .t562

theorem t563_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t563).mem (gathered (exponents .t563) c a) :=
  all_gathered c a hC ha .t563

theorem t564_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t564).mem (gathered (exponents .t564) c a) :=
  all_gathered c a hC ha .t564

theorem t566_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t566).mem (gathered (exponents .t566) c a) :=
  all_gathered c a hC ha .t566

theorem t567_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t567).mem (gathered (exponents .t567) c a) :=
  all_gathered c a hC ha .t567

theorem t568_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t568).mem (gathered (exponents .t568) c a) :=
  all_gathered c a hC ha .t568

theorem t569_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t569).mem (gathered (exponents .t569) c a) :=
  all_gathered c a hC ha .t569

theorem t570_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t570).mem (gathered (exponents .t570) c a) :=
  all_gathered c a hC ha .t570

theorem t571_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t571).mem (gathered (exponents .t571) c a) :=
  all_gathered c a hC ha .t571

theorem t572_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t572).mem (gathered (exponents .t572) c a) :=
  all_gathered c a hC ha .t572

theorem t573_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t573).mem (gathered (exponents .t573) c a) :=
  all_gathered c a hC ha .t573

theorem t576_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t576).mem (gathered (exponents .t576) c a) :=
  all_gathered c a hC ha .t576

theorem t577_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t577).mem (gathered (exponents .t577) c a) :=
  all_gathered c a hC ha .t577

theorem t578_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t578).mem (gathered (exponents .t578) c a) :=
  all_gathered c a hC ha .t578

theorem t579_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t579).mem (gathered (exponents .t579) c a) :=
  all_gathered c a hC ha .t579

theorem t580_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t580).mem (gathered (exponents .t580) c a) :=
  all_gathered c a hC ha .t580

theorem t581_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t581).mem (gathered (exponents .t581) c a) :=
  all_gathered c a hC ha .t581

theorem t582_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t582).mem (gathered (exponents .t582) c a) :=
  all_gathered c a hC ha .t582

theorem t585_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t585).mem (gathered (exponents .t585) c a) :=
  all_gathered c a hC ha .t585

theorem t586_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t586).mem (gathered (exponents .t586) c a) :=
  all_gathered c a hC ha .t586

theorem t587_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t587).mem (gathered (exponents .t587) c a) :=
  all_gathered c a hC ha .t587

theorem t588_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t588).mem (gathered (exponents .t588) c a) :=
  all_gathered c a hC ha .t588

theorem t593_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t593).mem (gathered (exponents .t593) c a) :=
  all_gathered c a hC ha .t593

theorem t594_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t594).mem (gathered (exponents .t594) c a) :=
  all_gathered c a hC ha .t594

theorem t595_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t595).mem (gathered (exponents .t595) c a) :=
  all_gathered c a hC ha .t595

theorem t600_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t600).mem (gathered (exponents .t600) c a) :=
  all_gathered c a hC ha .t600

theorem t601_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t601).mem (gathered (exponents .t601) c a) :=
  all_gathered c a hC ha .t601

theorem t602_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t602).mem (gathered (exponents .t602) c a) :=
  all_gathered c a hC ha .t602

theorem t605_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t605).mem (gathered (exponents .t605) c a) :=
  all_gathered c a hC ha .t605

theorem t606_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t606).mem (gathered (exponents .t606) c a) :=
  all_gathered c a hC ha .t606

theorem t607_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t607).mem (gathered (exponents .t607) c a) :=
  all_gathered c a hC ha .t607

theorem t610_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t610).mem (gathered (exponents .t610) c a) :=
  all_gathered c a hC ha .t610

theorem t611_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t611).mem (gathered (exponents .t611) c a) :=
  all_gathered c a hC ha .t611

theorem t614_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t614).mem (gathered (exponents .t614) c a) :=
  all_gathered c a hC ha .t614

theorem t617_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t617).mem (gathered (exponents .t617) c a) :=
  all_gathered c a hC ha .t617

theorem t620_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t620).mem (gathered (exponents .t620) c a) :=
  all_gathered c a hC ha .t620

theorem t621_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t621).mem (gathered (exponents .t621) c a) :=
  all_gathered c a hC ha .t621

theorem t622_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t622).mem (gathered (exponents .t622) c a) :=
  all_gathered c a hC ha .t622

theorem t623_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t623).mem (gathered (exponents .t623) c a) :=
  all_gathered c a hC ha .t623

theorem t624_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t624).mem (gathered (exponents .t624) c a) :=
  all_gathered c a hC ha .t624

theorem t625_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t625).mem (gathered (exponents .t625) c a) :=
  all_gathered c a hC ha .t625

theorem t626_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t626).mem (gathered (exponents .t626) c a) :=
  all_gathered c a hC ha .t626

theorem t627_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t627).mem (gathered (exponents .t627) c a) :=
  all_gathered c a hC ha .t627

theorem t628_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t628).mem (gathered (exponents .t628) c a) :=
  all_gathered c a hC ha .t628

theorem t631_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t631).mem (gathered (exponents .t631) c a) :=
  all_gathered c a hC ha .t631

theorem t632_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t632).mem (gathered (exponents .t632) c a) :=
  all_gathered c a hC ha .t632

theorem t633_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t633).mem (gathered (exponents .t633) c a) :=
  all_gathered c a hC ha .t633

theorem t634_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t634).mem (gathered (exponents .t634) c a) :=
  all_gathered c a hC ha .t634

theorem t635_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t635).mem (gathered (exponents .t635) c a) :=
  all_gathered c a hC ha .t635

theorem t636_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t636).mem (gathered (exponents .t636) c a) :=
  all_gathered c a hC ha .t636

theorem t637_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t637).mem (gathered (exponents .t637) c a) :=
  all_gathered c a hC ha .t637

theorem t638_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t638).mem (gathered (exponents .t638) c a) :=
  all_gathered c a hC ha .t638

theorem t641_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t641).mem (gathered (exponents .t641) c a) :=
  all_gathered c a hC ha .t641

theorem t642_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t642).mem (gathered (exponents .t642) c a) :=
  all_gathered c a hC ha .t642

theorem t643_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t643).mem (gathered (exponents .t643) c a) :=
  all_gathered c a hC ha .t643

theorem t644_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t644).mem (gathered (exponents .t644) c a) :=
  all_gathered c a hC ha .t644

theorem t645_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t645).mem (gathered (exponents .t645) c a) :=
  all_gathered c a hC ha .t645

theorem t650_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t650).mem (gathered (exponents .t650) c a) :=
  all_gathered c a hC ha .t650

theorem t651_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t651).mem (gathered (exponents .t651) c a) :=
  all_gathered c a hC ha .t651

theorem t652_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t652).mem (gathered (exponents .t652) c a) :=
  all_gathered c a hC ha .t652

theorem t658_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t658).mem (gathered (exponents .t658) c a) :=
  all_gathered c a hC ha .t658

theorem t659_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t659).mem (gathered (exponents .t659) c a) :=
  all_gathered c a hC ha .t659

theorem t660_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t660).mem (gathered (exponents .t660) c a) :=
  all_gathered c a hC ha .t660

theorem t662_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t662).mem (gathered (exponents .t662) c a) :=
  all_gathered c a hC ha .t662

theorem t663_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t663).mem (gathered (exponents .t663) c a) :=
  all_gathered c a hC ha .t663

theorem t666_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t666).mem (gathered (exponents .t666) c a) :=
  all_gathered c a hC ha .t666

theorem t667_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t667).mem (gathered (exponents .t667) c a) :=
  all_gathered c a hC ha .t667

theorem t670_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t670).mem (gathered (exponents .t670) c a) :=
  all_gathered c a hC ha .t670

theorem t671_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t671).mem (gathered (exponents .t671) c a) :=
  all_gathered c a hC ha .t671

theorem t674_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t674).mem (gathered (exponents .t674) c a) :=
  all_gathered c a hC ha .t674

theorem t680_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t680).mem (gathered (exponents .t680) c a) :=
  all_gathered c a hC ha .t680

theorem t681_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t681).mem (gathered (exponents .t681) c a) :=
  all_gathered c a hC ha .t681

theorem t682_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t682).mem (gathered (exponents .t682) c a) :=
  all_gathered c a hC ha .t682

theorem t683_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t683).mem (gathered (exponents .t683) c a) :=
  all_gathered c a hC ha .t683

theorem t684_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t684).mem (gathered (exponents .t684) c a) :=
  all_gathered c a hC ha .t684

theorem t685_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t685).mem (gathered (exponents .t685) c a) :=
  all_gathered c a hC ha .t685

theorem t686_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t686).mem (gathered (exponents .t686) c a) :=
  all_gathered c a hC ha .t686

theorem t687_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t687).mem (gathered (exponents .t687) c a) :=
  all_gathered c a hC ha .t687

theorem t688_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t688).mem (gathered (exponents .t688) c a) :=
  all_gathered c a hC ha .t688

theorem t691_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t691).mem (gathered (exponents .t691) c a) :=
  all_gathered c a hC ha .t691

theorem t692_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t692).mem (gathered (exponents .t692) c a) :=
  all_gathered c a hC ha .t692

theorem t693_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t693).mem (gathered (exponents .t693) c a) :=
  all_gathered c a hC ha .t693

theorem t694_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t694).mem (gathered (exponents .t694) c a) :=
  all_gathered c a hC ha .t694

theorem t695_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t695).mem (gathered (exponents .t695) c a) :=
  all_gathered c a hC ha .t695

theorem t696_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t696).mem (gathered (exponents .t696) c a) :=
  all_gathered c a hC ha .t696

theorem t701_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t701).mem (gathered (exponents .t701) c a) :=
  all_gathered c a hC ha .t701

theorem t702_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t702).mem (gathered (exponents .t702) c a) :=
  all_gathered c a hC ha .t702

theorem t710_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t710).mem (gathered (exponents .t710) c a) :=
  all_gathered c a hC ha .t710

theorem t711_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t711).mem (gathered (exponents .t711) c a) :=
  all_gathered c a hC ha .t711

theorem t713_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t713).mem (gathered (exponents .t713) c a) :=
  all_gathered c a hC ha .t713

theorem t714_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t714).mem (gathered (exponents .t714) c a) :=
  all_gathered c a hC ha .t714

theorem t716_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t716).mem (gathered (exponents .t716) c a) :=
  all_gathered c a hC ha .t716

theorem t717_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t717).mem (gathered (exponents .t717) c a) :=
  all_gathered c a hC ha .t717

theorem t719_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t719).mem (gathered (exponents .t719) c a) :=
  all_gathered c a hC ha .t719

theorem t722_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t722).mem (gathered (exponents .t722) c a) :=
  all_gathered c a hC ha .t722

theorem t725_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t725).mem (gathered (exponents .t725) c a) :=
  all_gathered c a hC ha .t725

theorem t731_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t731).mem (gathered (exponents .t731) c a) :=
  all_gathered c a hC ha .t731

theorem t732_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t732).mem (gathered (exponents .t732) c a) :=
  all_gathered c a hC ha .t732

theorem t733_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t733).mem (gathered (exponents .t733) c a) :=
  all_gathered c a hC ha .t733

theorem t734_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t734).mem (gathered (exponents .t734) c a) :=
  all_gathered c a hC ha .t734

theorem t735_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t735).mem (gathered (exponents .t735) c a) :=
  all_gathered c a hC ha .t735

theorem t736_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t736).mem (gathered (exponents .t736) c a) :=
  all_gathered c a hC ha .t736

theorem t737_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t737).mem (gathered (exponents .t737) c a) :=
  all_gathered c a hC ha .t737

theorem t742_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t742).mem (gathered (exponents .t742) c a) :=
  all_gathered c a hC ha .t742

theorem t743_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t743).mem (gathered (exponents .t743) c a) :=
  all_gathered c a hC ha .t743

theorem t752_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t752).mem (gathered (exponents .t752) c a) :=
  all_gathered c a hC ha .t752

theorem t754_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t754).mem (gathered (exponents .t754) c a) :=
  all_gathered c a hC ha .t754

theorem t756_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t756).mem (gathered (exponents .t756) c a) :=
  all_gathered c a hC ha .t756

theorem t758_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t758).mem (gathered (exponents .t758) c a) :=
  all_gathered c a hC ha .t758

theorem t760_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t760).mem (gathered (exponents .t760) c a) :=
  all_gathered c a hC ha .t760

theorem t769_gathered (c : TermIndex → ℝ) (a : Fin 3 → ℝ)
    (hC : ∀ t, (sourceInterval t).mem (c t)) (ha : ∀ i, (centerInterval i).mem (a i)) :
    (coefficientInterval .t769).mem (gathered (exponents .t769) c a) :=
  all_gathered c a hC ha .t769

end ThomsonNine.AAAFixedComplete
