import RequestProject.DVPLogBracket

/-!
# The `log n` bracket table, `n = 201..250` (rung-109 extension)
-/

open Finset

noncomputable section

namespace CriticalLinePhasor.DVP

theorem log_br_201 :
    ((53033049/10000000 : ℚ) : ℝ) ≤ Real.log (201 : ℕ)
      ∧ Real.log (201 : ℕ) ≤ ((1060661/200000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_202 :
    ((13270669/2500000 : ℚ) : ℝ) ≤ Real.log (202 : ℕ)
      ∧ Real.log (202 : ℕ) ≤ ((53082677/10000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_203 :
    ((53132059/10000000 : ℚ) : ℝ) ≤ Real.log (203 : ℕ)
      ∧ Real.log (203 : ℕ) ≤ ((2656603/500000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_204 :
    ((53181199/10000000 : ℚ) : ℝ) ≤ Real.log (204 : ℕ)
      ∧ Real.log (204 : ℕ) ≤ ((132953/25000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_205 :
    ((53230099/10000000 : ℚ) : ℝ) ≤ Real.log (205 : ℕ)
      ∧ Real.log (205 : ℕ) ≤ ((532301/100000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_206 :
    ((53278761/10000000 : ℚ) : ℝ) ≤ Real.log (206 : ℕ)
      ∧ Real.log (206 : ℕ) ≤ ((26639381/5000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_207 :
    ((53327187/10000000 : ℚ) : ℝ) ≤ Real.log (207 : ℕ)
      ∧ Real.log (207 : ℕ) ≤ ((13331797/2500000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_208 :
    ((2668769/500000 : ℚ) : ℝ) ≤ Real.log (208 : ℕ)
      ∧ Real.log (208 : ℕ) ≤ ((53375381/10000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_209 :
    ((26711671/5000000 : ℚ) : ℝ) ≤ Real.log (209 : ℕ)
      ∧ Real.log (209 : ℕ) ≤ ((53423343/10000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_210 :
    ((2138843/400000 : ℚ) : ℝ) ≤ Real.log (210 : ℕ)
      ∧ Real.log (210 : ℕ) ≤ ((13367769/2500000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_211 :
    ((53518581/10000000 : ℚ) : ℝ) ≤ Real.log (211 : ℕ)
      ∧ Real.log (211 : ℕ) ≤ ((26759291/5000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_212 :
    ((26782931/5000000 : ℚ) : ℝ) ≤ Real.log (212 : ℕ)
      ∧ Real.log (212 : ℕ) ≤ ((53565863/10000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_213 :
    ((53612921/10000000 : ℚ) : ℝ) ≤ Real.log (213 : ℕ)
      ∧ Real.log (213 : ℕ) ≤ ((26806461/5000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_214 :
    ((670747/125000 : ℚ) : ℝ) ≤ Real.log (214 : ℕ)
      ∧ Real.log (214 : ℕ) ≤ ((53659761/10000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_215 :
    ((2685319/500000 : ℚ) : ℝ) ≤ Real.log (215 : ℕ)
      ∧ Real.log (215 : ℕ) ≤ ((53706381/10000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_216 :
    ((3359549/625000 : ℚ) : ℝ) ≤ Real.log (216 : ℕ)
      ∧ Real.log (216 : ℕ) ≤ ((10750557/2000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_217 :
    ((53798973/10000000 : ℚ) : ℝ) ≤ Real.log (217 : ℕ)
      ∧ Real.log (217 : ℕ) ≤ ((26899487/5000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_218 :
    ((1076899/200000 : ℚ) : ℝ) ≤ Real.log (218 : ℕ)
      ∧ Real.log (218 : ℕ) ≤ ((53844951/10000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_219 :
    ((53890717/10000000 : ℚ) : ℝ) ≤ Real.log (219 : ℕ)
      ∧ Real.log (219 : ℕ) ≤ ((26945359/5000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_220 :
    ((2157451/400000 : ℚ) : ℝ) ≤ Real.log (220 : ℕ)
      ∧ Real.log (220 : ℕ) ≤ ((13484069/2500000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_221 :
    ((53981627/10000000 : ℚ) : ℝ) ≤ Real.log (221 : ℕ)
      ∧ Real.log (221 : ℕ) ≤ ((13495407/2500000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_222 :
    ((54026773/10000000 : ℚ) : ℝ) ≤ Real.log (222 : ℕ)
      ∧ Real.log (222 : ℕ) ≤ ((27013387/5000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_223 :
    ((54071717/10000000 : ℚ) : ℝ) ≤ Real.log (223 : ℕ)
      ∧ Real.log (223 : ℕ) ≤ ((27035859/5000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_224 :
    ((2705823/500000 : ℚ) : ℝ) ≤ Real.log (224 : ℕ)
      ∧ Real.log (224 : ℕ) ≤ ((54116461/10000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_225 :
    ((13540251/2500000 : ℚ) : ℝ) ≤ Real.log (225 : ℕ)
      ∧ Real.log (225 : ℕ) ≤ ((10832201/2000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_226 :
    ((54205349/10000000 : ℚ) : ℝ) ≤ Real.log (226 : ℕ)
      ∧ Real.log (226 : ℕ) ≤ ((54205351/10000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_227 :
    ((108499/20000 : ℚ) : ℝ) ≤ Real.log (227 : ℕ)
      ∧ Real.log (227 : ℕ) ≤ ((54249501/10000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_228 :
    ((3393341/625000 : ℚ) : ℝ) ≤ Real.log (228 : ℕ)
      ∧ Real.log (228 : ℕ) ≤ ((54293457/10000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_229 :
    ((2716861/500000 : ℚ) : ℝ) ≤ Real.log (229 : ℕ)
      ∧ Real.log (229 : ℕ) ≤ ((54337221/10000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_230 :
    ((54380793/10000000 : ℚ) : ℝ) ≤ Real.log (230 : ℕ)
      ∧ Real.log (230 : ℕ) ≤ ((27190397/5000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_231 :
    ((54424177/10000000 : ℚ) : ℝ) ≤ Real.log (231 : ℕ)
      ∧ Real.log (231 : ℕ) ≤ ((27212089/5000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_232 :
    ((54467373/10000000 : ℚ) : ℝ) ≤ Real.log (232 : ℕ)
      ∧ Real.log (232 : ℕ) ≤ ((27233687/5000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_233 :
    ((3406899/625000 : ℚ) : ℝ) ≤ Real.log (233 : ℕ)
      ∧ Real.log (233 : ℕ) ≤ ((10902077/2000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_234 :
    ((54553211/10000000 : ℚ) : ℝ) ≤ Real.log (234 : ℕ)
      ∧ Real.log (234 : ℕ) ≤ ((13638303/2500000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_235 :
    ((10919171/2000000 : ℚ) : ℝ) ≤ Real.log (235 : ℕ)
      ∧ Real.log (235 : ℕ) ≤ ((3412241/625000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_236 :
    ((27319159/5000000 : ℚ) : ℝ) ≤ Real.log (236 : ℕ)
      ∧ Real.log (236 : ℕ) ≤ ((54638319/10000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_237 :
    ((54680601/10000000 : ℚ) : ℝ) ≤ Real.log (237 : ℕ)
      ∧ Real.log (237 : ℕ) ≤ ((27340301/5000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_238 :
    ((27361353/5000000 : ℚ) : ℝ) ≤ Real.log (238 : ℕ)
      ∧ Real.log (238 : ℕ) ≤ ((54722707/10000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_239 :
    ((10952927/2000000 : ℚ) : ℝ) ≤ Real.log (239 : ℕ)
      ∧ Real.log (239 : ℕ) ≤ ((13691159/2500000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_240 :
    ((54806389/10000000 : ℚ) : ℝ) ≤ Real.log (240 : ℕ)
      ∧ Real.log (240 : ℕ) ≤ ((5480639/1000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_241 :
    ((54847969/10000000 : ℚ) : ℝ) ≤ Real.log (241 : ℕ)
      ∧ Real.log (241 : ℕ) ≤ ((5484797/1000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_242 :
    ((54889377/10000000 : ℚ) : ℝ) ≤ Real.log (242 : ℕ)
      ∧ Real.log (242 : ℕ) ≤ ((27444689/5000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_243 :
    ((27465307/5000000 : ℚ) : ℝ) ≤ Real.log (243 : ℕ)
      ∧ Real.log (243 : ℕ) ≤ ((10986123/2000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_244 :
    ((27485841/5000000 : ℚ) : ℝ) ≤ Real.log (244 : ℕ)
      ∧ Real.log (244 : ℕ) ≤ ((54971683/10000000 : ℚ) : ℝ) :=
  log_bracket 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_245 :
    ((55012581/10000000 : ℚ) : ℝ) ≤ Real.log (245 : ℕ)
      ∧ Real.log (245 : ℕ) ≤ ((55012583/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_246 :
    ((11010663/2000000 : ℚ) : ℝ) ≤ Real.log (246 : ℕ)
      ∧ Real.log (246 : ℕ) ≤ ((13763329/2500000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_247 :
    ((55093883/10000000 : ℚ) : ℝ) ≤ Real.log (247 : ℕ)
      ∧ Real.log (247 : ℕ) ≤ ((13773471/2500000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_248 :
    ((55134287/10000000 : ℚ) : ℝ) ≤ Real.log (248 : ℕ)
      ∧ Real.log (248 : ℕ) ≤ ((3445893/625000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_249 :
    ((431051/78125 : ℚ) : ℝ) ≤ Real.log (249 : ℕ)
      ∧ Real.log (249 : ℕ) ≤ ((55174529/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_250 :
    ((55214609/10000000 : ℚ) : ℝ) ≤ Real.log (250 : ℕ)
      ∧ Real.log (250 : ℕ) ≤ ((5521461/1000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.log_br_250
end AxiomAudit
