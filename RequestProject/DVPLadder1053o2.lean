import RequestProject.DVPLadder1016o2
import RequestProject.DVPExhaustion1053o2
import RequestProject.DVPStation509
import RequestProject.DVPStation511
import RequestProject.DVPStation512
import RequestProject.DVPStation513
import RequestProject.DVPStation515
import RequestProject.DVPStation516
import RequestProject.DVPStation518
import RequestProject.DVPStation519
import RequestProject.DVPStation521
import RequestProject.DVPStation522
import RequestProject.DVPStation523
import RequestProject.DVPStation1049o2
import RequestProject.DVPStation526

/-!
# Rung-526.5: on-line to 1053/2, channel to 526
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale
open CriticalLinePhasor.FoliatedPolarization

noncomputable section

namespace CriticalLinePhasor.DVP

set_option maxRecDepth 16384 in
/-- The two hundred seven station heights. -/
def ladder1053o2T (i : Fin 289) : ℝ :=
  if i.val = 0 then 11
  else if i.val = 1 then 18
  else if i.val = 2 then 23
  else if i.val = 3 then 28
  else if i.val = 4 then 32
  else if i.val = 5 then 35
  else if i.val = 6 then 39
  else if i.val = 7 then 42
  else if i.val = 8 then 46
  else if i.val = 9 then 49
  else if i.val = 10 then 52
  else if i.val = 11 then 55
  else if i.val = 12 then 58
  else if i.val = 13 then 60
  else if i.val = 14 then 62
  else if i.val = 15 then 66
  else if i.val = 16 then 68
  else if i.val = 17 then 71
  else if i.val = 18 then 74
  else if i.val = 19 then 76
  else if i.val = 20 then 78
  else if i.val = 21 then 80
  else if i.val = 22 then 84
  else if i.val = 23 then 86
  else if i.val = 24 then 88
  else if i.val = 25 then 90
  else if i.val = 26 then 93
  else if i.val = 27 then 95
  else if i.val = 28 then 97
  else if i.val = 29 then 100
  else if i.val = 30 then 102
  else if i.val = 31 then 105
  else if i.val = 32 then 106
  else if i.val = 33 then 108
  else if i.val = 34 then 223/2
  else if i.val = 35 then 113
  else if i.val = 36 then 115
  else if i.val = 37 then 118
  else if i.val = 38 then 120
  else if i.val = 39 then 122
  else if i.val = 40 then 247/2
  else if i.val = 41 then 125
  else if i.val = 42 then 128
  else if i.val = 43 then 130
  else if i.val = 44 then 132
  else if i.val = 45 then 134
  else if i.val = 46 then 136
  else if i.val = 47 then 139
  else if i.val = 48 then 281/2
  else if i.val = 49 then 142
  else if i.val = 50 then 144
  else if i.val = 51 then 147
  else if i.val = 52 then 149
  else if i.val = 53 then 301/2
  else if i.val = 54 then 152
  else if i.val = 55 then 154
  else if i.val = 56 then 157
  else if i.val = 57 then 158
  else if i.val = 58 then 160
  else if i.val = 59 then 162
  else if i.val = 60 then 164
  else if i.val = 61 then 166
  else if i.val = 62 then 168
  else if i.val = 63 then 339/2
  else if i.val = 64 then 172
  else if i.val = 65 then 174
  else if i.val = 66 then 176
  else if i.val = 67 then 177
  else if i.val = 68 then 179
  else if i.val = 69 then 181
  else if i.val = 70 then 183
  else if i.val = 71 then 741/4
  else if i.val = 72 then 186
  else if i.val = 73 then 188
  else if i.val = 74 then 191
  else if i.val = 75 then 385/2
  else if i.val = 76 then 194
  else if i.val = 77 then 196
  else if i.val = 78 then 395/2
  else if i.val = 79 then 199
  else if i.val = 80 then 202
  else if i.val = 81 then 203
  else if i.val = 82 then 205
  else if i.val = 83 then 207
  else if i.val = 84 then 209
  else if i.val = 85 then 211
  else if i.val = 86 then 212
  else if i.val = 87 then 214
  else if i.val = 88 then 215
  else if i.val = 89 then 217
  else if i.val = 90 then 220
  else if i.val = 91 then 221
  else if i.val = 92 then 223
  else if i.val = 93 then 449/2
  else if i.val = 94 then 226
  else if i.val = 95 then 228
  else if i.val = 96 then 230
  else if i.val = 97 then 463/2
  else if i.val = 98 then 233
  else if i.val = 99 then 235
  else if i.val = 100 then 237
  else if i.val = 101 then 239
  else if i.val = 102 then 240
  else if i.val = 103 then 242
  else if i.val = 104 then 243
  else if i.val = 105 then 246
  else if i.val = 106 then 495/2
  else if i.val = 107 then 249
  else if i.val = 108 then 250
  else if i.val = 109 then 252
  else if i.val = 110 then 254
  else if i.val = 111 then 256
  else if i.val = 112 then 257
  else if i.val = 113 then 259
  else if i.val = 114 then 521/2
  else if i.val = 115 then 262
  else if i.val = 116 then 264
  else if i.val = 117 then 266
  else if i.val = 118 then 267
  else if i.val = 119 then 269
  else if i.val = 120 then 271
  else if i.val = 121 then 272
  else if i.val = 122 then 274
  else if i.val = 123 then 276
  else if i.val = 124 then 277
  else if i.val = 125 then 279
  else if i.val = 126 then 280
  else if i.val = 127 then 283
  else if i.val = 128 then 284
  else if i.val = 129 then 286
  else if i.val = 130 then 287
  else if i.val = 131 then 289
  else if i.val = 132 then 290
  else if i.val = 133 then 293
  else if i.val = 134 then 294
  else if i.val = 135 then 1181/4
  else if i.val = 136 then 297
  else if i.val = 137 then 299
  else if i.val = 138 then 301
  else if i.val = 139 then 302
  else if i.val = 140 then 304
  else if i.val = 141 then 1221/4
  else if i.val = 142 then 307
  else if i.val = 143 then 308
  else if i.val = 144 then 1242/4
  else if i.val = 145 then 312
  else if i.val = 146 then 313
  else if i.val = 147 then 315
  else if i.val = 148 then 317
  else if i.val = 149 then 318
  else if i.val = 150 then 320
  else if i.val = 151 then 643/2
  else if i.val = 152 then 323
  else if i.val = 153 then 324
  else if i.val = 154 then 326
  else if i.val = 155 then 328
  else if i.val = 156 then 659/2
  else if i.val = 157 then 331
  else if i.val = 158 then 333
  else if i.val = 159 then 334
  else if i.val = 160 then 335
  else if i.val = 161 then 338
  else if i.val = 162 then 339
  else if i.val = 163 then 340
  else if i.val = 164 then 342
  else if i.val = 165 then 343
  else if i.val = 166 then 345
  else if i.val = 167 then 347
  else if i.val = 168 then 348
  else if i.val = 169 then 350
  else if i.val = 170 then 351
  else if i.val = 171 then 353
  else if i.val = 172 then 355
  else if i.val = 173 then 713/2
  else if i.val = 174 then 715/2
  else if i.val = 175 then 359
  else if i.val = 176 then 361
  else if i.val = 177 then 362
  else if i.val = 178 then 364
  else if i.val = 179 then 365
  else if i.val = 180 then 367
  else if i.val = 181 then 737/2
  else if i.val = 182 then 739/2
  else if i.val = 183 then 371
  else if i.val = 184 then 747/2
  else if i.val = 185 then 375
  else if i.val = 186 then 376
  else if i.val = 187 then 378
  else if i.val = 188 then 379
  else if i.val = 189 then 381
  else if i.val = 190 then 382
  else if i.val = 191 then 384
  else if i.val = 192 then 771/2
  else if i.val = 193 then 387
  else if i.val = 194 then 388
  else if i.val = 195 then 389
  else if i.val = 196 then 392
  else if i.val = 197 then 393
  else if i.val = 198 then 394
  else if i.val = 199 then 396
  else if i.val = 200 then 397
  else if i.val = 201 then 399
  else if i.val = 202 then 401
  else if i.val = 203 then 402
  else if i.val = 204 then 404
  else if i.val = 205 then 405
  else if i.val = 206 then 406
  else if i.val = 207 then 408
  else if i.val = 208 then 410
  else if i.val = 209 then 411
  else if i.val = 210 then 413
  else if i.val = 211 then 414
  else if i.val = 212 then 1661/4
  else if i.val = 213 then 416
  else if i.val = 214 then 419
  else if i.val = 215 then 1681/4
  else if i.val = 216 then 421
  else if i.val = 217 then 423
  else if i.val = 218 then 424
  else if i.val = 219 then 426
  else if i.val = 220 then 428
  else if i.val = 221 then 429
  else if i.val = 222 then 431
  else if i.val = 223 then 1727/4
  else if i.val = 224 then 433
  else if i.val = 225 then 435
  else if i.val = 226 then 437
  else if i.val = 227 then 438
  else if i.val = 228 then 439
  else if i.val = 229 then 441
  else if i.val = 230 then 442
  else if i.val = 231 then 444
  else if i.val = 232 then 445
  else if i.val = 233 then 1789/4
  else if i.val = 234 then 448
  else if i.val = 235 then 899/2
  else if i.val = 236 then 451
  else if i.val = 237 then 452
  else if i.val = 238 then 909/2
  else if i.val = 239 then 456
  else if i.val = 240 then 457
  else if i.val = 241 then 459
  else if i.val = 242 then 1839/4
  else if i.val = 243 then 461
  else if i.val = 244 then 463
  else if i.val = 245 then 465
  else if i.val = 246 then 466
  else if i.val = 247 then 467
  else if i.val = 248 then 469
  else if i.val = 249 then 470
  else if i.val = 250 then 472
  else if i.val = 251 then 473
  else if i.val = 252 then 475
  else if i.val = 253 then 476
  else if i.val = 254 then 477
  else if i.val = 255 then 957/2
  else if i.val = 256 then 480
  else if i.val = 257 then 482
  else if i.val = 258 then 1933/4
  else if i.val = 259 then 485
  else if i.val = 260 then 486
  else if i.val = 261 then 487
  else if i.val = 262 then 489
  else if i.val = 263 then 491
  else if i.val = 264 then 492
  else if i.val = 265 then 1975/4
  else if i.val = 266 then 495
  else if i.val = 267 then 496
  else if i.val = 268 then 497
  else if i.val = 269 then 499
  else if i.val = 270 then 501
  else if i.val = 271 then 1004/2
  else if i.val = 272 then 503
  else if i.val = 273 then 505
  else if i.val = 274 then 506
  else if i.val = 275 then 507
  else if i.val = 276 then 509
  else if i.val = 277 then 511
  else if i.val = 278 then 512
  else if i.val = 279 then 513
  else if i.val = 280 then 515
  else if i.val = 281 then 516
  else if i.val = 282 then 518
  else if i.val = 283 then 519
  else if i.val = 284 then 521
  else if i.val = 285 then 522
  else if i.val = 286 then 523
  else if i.val = 287 then 1049/2
  else 526

set_option maxRecDepth 16384 in
set_option maxHeartbeats 102400000 in
/-- **The 289-station ladder is inhabited.** -/
theorem ladder1053o2Data_holds : LadderData1053o2 := by
  refine ⟨ladder1053o2T, ?_, ?_, ?_⟩
  · rw [Fin.strictMono_iff_lt_succ]
    intro i
    fin_cases i <;> norm_num [ladder1053o2T]
  · intro i
    fin_cases i <;> constructor <;> norm_num [ladder1053o2T]
  · intro i
    fin_cases i
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_11_sign station_18_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_18_sign station_23_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_23_sign station_28_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_28_sign station_32_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_32_sign station_35_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_35_sign station_39_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_39_sign station_42_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_42_sign station_46_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_46_sign station_49_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_49_sign station_52_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_52_sign station_55_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_55_sign station_58_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_58_sign station_60_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_60_sign station_62_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_62_sign station_66_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_66_sign station_68_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_68_sign station_71_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_71_sign station_74_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_74_sign station_76_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_76_sign station_78_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_78_sign station_80_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_80_sign station_84_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_84_sign station_86_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_86_sign station_88_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_88_sign station_90_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_90_sign station_93_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_93_sign station_95_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_95_sign station_97_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_97_sign station_100_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_100_sign station_102_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_102_sign station_105_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_105_sign station_106_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_106_sign station_108_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_108_sign station_223o2_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_223o2_sign station_113_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_113_sign station_115_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_115_sign station_118_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_118_sign station_120_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_120_sign station_122_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_122_sign station_247o2_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_247o2_sign station_125_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_125_sign station_128_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_128_sign station_130_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_130_sign station_132_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_132_sign station_134_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_134_sign station_136_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_136_sign station_139_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_139_sign station_281o2_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_281o2_sign station_142_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_142_sign station_144_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_144_sign station_147_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_147_sign station_149_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_149_sign station_301o2_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_301o2_sign station_152_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_152_sign station_154_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_154_sign station_157_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_157_sign station_158_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_158_sign station_160_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_160_sign station_162_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_162_sign station_164_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_164_sign station_166_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_166_sign station_168_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_168_sign station_339o2_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_339o2_sign station_172_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_172_sign station_174_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_174_sign station_176_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_176_sign station_177_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_177_sign station_179_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_179_sign station_181_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_181_sign station_183_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_183_sign station_741o4_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_741o4_sign station_186_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_186_sign station_188_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_188_sign station_191_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_191_sign station_385o2_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_385o2_sign station_194_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_194_sign station_196_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_196_sign station_395o2_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_395o2_sign station_199_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_199_sign station_202_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_202_sign station_203_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_203_sign station_205_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_205_sign station_207_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_207_sign station_209_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_209_sign station_211_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_211_sign station_212_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_212_sign station_214_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_214_sign station_215_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_215_sign station_217_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_217_sign station_220_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_220_sign station_221_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_221_sign station_223_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_223_sign station_449o2_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_449o2_sign station_226_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_226_sign station_228_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_228_sign station_230_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_230_sign station_463o2_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_463o2_sign station_233_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_233_sign station_235_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_235_sign station_237_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_237_sign station_239_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_239_sign station_240_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_240_sign station_242_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_242_sign station_243_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_243_sign station_246_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_246_sign station_495o2_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_495o2_sign station_249_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_249_sign station_250_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_250_sign station_252_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_252_sign station_254_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_254_sign station_256_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_256_sign station_257_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_257_sign station_259_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_259_sign station_521o2_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_521o2_sign station_262_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_262_sign station_264_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_264_sign station_266_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_266_sign station_267_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_267_sign station_269_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_269_sign station_271_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_271_sign station_272_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_272_sign station_274_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_274_sign station_276_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_276_sign station_277_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_277_sign station_279_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_279_sign station_280_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_280_sign station_283_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_283_sign station_284_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_284_sign station_286_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_286_sign station_287_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_287_sign station_289_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_289_sign station_290_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_290_sign station_293_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_293_sign station_294_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_294_sign station_1181o4_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_1181o4_sign station_297_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_297_sign station_299_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_299_sign station_301_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_301_sign station_302_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_302_sign station_304_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_304_sign station_1221o4_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_1221o4_sign station_307_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_307_sign station_308_sign
    · norm_num [ladder1053o2T]
      have h1 : hardyG ((1242:ℝ)/4) < 0 := by
        have h := station_1242o4_sign
        push_cast at h
        exact h
      rw [show ((1242:ℝ)/4) = 621/2 by norm_num] at h1
      exact mul_neg_of_pos_of_neg (by exact_mod_cast station_308_sign) h1
    · norm_num [ladder1053o2T]
      have h1 : hardyG ((1242:ℝ)/4) < 0 := by
        have h := station_1242o4_sign
        push_cast at h
        exact h
      rw [show ((1242:ℝ)/4) = 621/2 by norm_num] at h1
      exact mul_neg_of_neg_of_pos h1 (by exact_mod_cast station_312_sign)
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_312_sign station_313_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_313_sign station_315_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_315_sign station_317_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_317_sign station_318_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_318_sign station_320_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_320_sign station_643o2_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_643o2_sign station_323_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_323_sign station_324_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_324_sign station_326_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_326_sign station_328_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_328_sign station_659o2_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_659o2_sign station_331_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_331_sign station_333_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_333_sign station_334_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_334_sign station_335_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_335_sign station_338_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_338_sign station_339_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_339_sign station_340_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_340_sign station_342_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_342_sign station_343_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_343_sign station_345_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_345_sign station_347_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_347_sign station_348_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_348_sign station_350_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_350_sign station_351_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_351_sign station_353_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_353_sign station_355_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_355_sign station_713o2_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_713o2_sign station_715o2_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_715o2_sign station_359_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_359_sign station_361_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_361_sign station_362_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_362_sign station_364_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_364_sign station_365_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_365_sign station_367_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_367_sign station_737o2_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_737o2_sign station_739o2_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_739o2_sign station_371_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_371_sign station_747o2_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_747o2_sign station_375_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_375_sign station_376_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_376_sign station_378_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_378_sign station_379_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_379_sign station_381_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_381_sign station_382_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_382_sign station_384_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_384_sign station_771o2_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_771o2_sign station_387_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_387_sign station_388_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_388_sign station_389_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_389_sign station_392_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_392_sign station_393_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_393_sign station_394_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_394_sign station_396_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_396_sign station_397_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_397_sign station_399_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_399_sign station_401_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_401_sign station_402_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_402_sign station_404_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_404_sign station_405_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_405_sign station_406_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_406_sign station_408_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_408_sign station_410_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_410_sign station_411_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_411_sign station_413_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_413_sign station_414_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_414_sign station_1661o4_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_1661o4_sign station_416_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_416_sign station_419_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_419_sign station_1681o4_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_1681o4_sign station_421_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_421_sign station_423_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_423_sign station_424_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_424_sign station_426_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_426_sign station_428_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_428_sign station_429_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_429_sign station_431_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_431_sign station_1727o4_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_1727o4_sign station_433_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_433_sign station_435_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_435_sign station_437_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_437_sign station_438_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_438_sign station_439_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_439_sign station_441_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_441_sign station_442_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_442_sign station_444_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_444_sign station_445_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_445_sign station_1789o4_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_1789o4_sign station_448_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_448_sign station_899o2_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_899o2_sign station_451_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_451_sign station_452_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_452_sign station_909o2_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_909o2_sign station_456_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_456_sign station_457_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_457_sign station_459_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_459_sign station_1839o4_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_1839o4_sign station_461_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_461_sign station_463_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_463_sign station_465_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_465_sign station_466_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_466_sign station_467_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_467_sign station_469_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_469_sign station_470_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_470_sign station_472_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_472_sign station_473_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_473_sign station_475_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_475_sign station_476_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_476_sign station_477_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_477_sign station_957o2_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_957o2_sign station_480_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_480_sign station_482_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_482_sign station_1933o4_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_1933o4_sign station_485_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_485_sign station_486_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_486_sign station_487_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_487_sign station_489_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_489_sign station_491_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_491_sign station_492_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_492_sign station_1975o4_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_1975o4_sign station_495_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_495_sign station_496_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_496_sign station_497_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_497_sign station_499_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_499_sign station_501_sign
    · norm_num [ladder1053o2T]
      have h1 : (0:ℝ) < hardyG ((1004:ℝ)/2) := by
        have h := station_1004o2_sign
        push_cast at h
        exact h
      rw [show ((1004:ℝ)/2) = 502 by norm_num] at h1
      exact mul_neg_of_neg_of_pos (by exact_mod_cast station_501_sign) h1
    · norm_num [ladder1053o2T]
      have h1 : (0:ℝ) < hardyG ((1004:ℝ)/2) := by
        have h := station_1004o2_sign
        push_cast at h
        exact h
      rw [show ((1004:ℝ)/2) = 502 by norm_num] at h1
      exact mul_neg_of_pos_of_neg h1 (by exact_mod_cast station_503_sign)
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_503_sign station_505_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_505_sign station_506_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_506_sign station_507_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_507_sign station_509_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_509_sign station_511_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_511_sign station_512_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_512_sign station_513_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_513_sign station_515_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_515_sign station_516_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_516_sign station_518_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_518_sign station_519_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_519_sign station_521_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_521_sign station_522_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_522_sign station_523_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_neg_of_pos station_523_sign station_1049o2_sign
    · norm_num [ladder1053o2T]
      exact_mod_cast mul_neg_of_pos_of_neg station_1049o2_sign station_526_sign

/-- **Every nontrivial zero of ordinate `|γ| ≤ 1053/2` is on the line.** -/
theorem online_below_1053o2 :
    ∀ ρ ∈ ZD.NontrivialZeros, |ρ.im| ≤ 1053/2 → ρ.re = 1/2 :=
  online_below_1053o2_of_ladder ladder1053o2Data_holds

/-- **The channel to height 416.5, unconditional.** -/
theorem seat_channel_to_526 {w : ℂ}
    (hw : (1 / 2 + Complex.I * w) ∉ ZD.NontrivialZeros)
    (hw' : (1 / 2 + Complex.I * (starRingEnd ℂ) w) ∉ ZD.NontrivialZeros)
    (him : w - (starRingEnd ℂ) w ≠ 0)
    (hre : |w.re| ≤ 526) :
    0 ≤ (∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
        (ZD.xiOrderNat ρ.val : ℂ) *
          ((spectralCoord ρ.val - w)⁻¹ *
            (spectralCoord ρ.val - (starRingEnd ℂ) w)⁻¹)).re :=
  seat_channel_of_online_range (T := 1053/2) online_below_1053o2 hw hw' him
    (by linarith)

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.ladder1053o2Data_holds
#print axioms CriticalLinePhasor.DVP.online_below_1053o2
#print axioms CriticalLinePhasor.DVP.seat_channel_to_526
end AxiomAudit
