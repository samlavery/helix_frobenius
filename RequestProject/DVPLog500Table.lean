import RequestProject.DVPLogBracket

/-!
# Natural-log brackets 251-500 (rung-154.5 station support)
-/

noncomputable section

namespace CriticalLinePhasor.DVP

theorem log_br_251 :
    ((55254529/10000000 : ℚ) : ℝ) ≤ Real.log (251 : ℕ)
      ∧ Real.log (251 : ℕ) ≤ ((5525453/1000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_252 :
    ((5529429/1000000 : ℚ) : ℝ) ≤ Real.log (252 : ℕ)
      ∧ Real.log (252 : ℕ) ≤ ((55294291/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_253 :
    ((27666947/5000000 : ℚ) : ℝ) ≤ Real.log (253 : ℕ)
      ∧ Real.log (253 : ℕ) ≤ ((11066779/2000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_254 :
    ((27686671/5000000 : ℚ) : ℝ) ≤ Real.log (254 : ℕ)
      ∧ Real.log (254 : ℕ) ≤ ((55373343/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_255 :
    ((11082527/2000000 : ℚ) : ℝ) ≤ Real.log (255 : ℕ)
      ∧ Real.log (255 : ℕ) ≤ ((13853159/2500000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_256 :
    ((27725887/5000000 : ℚ) : ℝ) ≤ Real.log (256 : ℕ)
      ∧ Real.log (256 : ℕ) ≤ ((2218071/400000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_257 :
    ((1387269/250000 : ℚ) : ℝ) ≤ Real.log (257 : ℕ)
      ∧ Real.log (257 : ℕ) ≤ ((55490761/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_258 :
    ((11105919/2000000 : ℚ) : ℝ) ≤ Real.log (258 : ℕ)
      ∧ Real.log (258 : ℕ) ≤ ((13882399/2500000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_259 :
    ((1389207/250000 : ℚ) : ℝ) ≤ Real.log (259 : ℕ)
      ∧ Real.log (259 : ℕ) ≤ ((55568281/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_260 :
    ((1737713/312500 : ℚ) : ℝ) ≤ Real.log (260 : ℕ)
      ∧ Real.log (260 : ℕ) ≤ ((55606817/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_261 :
    ((13911301/2500000 : ℚ) : ℝ) ≤ Real.log (261 : ℕ)
      ∧ Real.log (261 : ℕ) ≤ ((11129041/2000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_262 :
    ((13920861/2500000 : ℚ) : ℝ) ≤ Real.log (262 : ℕ)
      ∧ Real.log (262 : ℕ) ≤ ((55683447/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_263 :
    ((2786077/500000 : ℚ) : ℝ) ≤ Real.log (263 : ℕ)
      ∧ Real.log (263 : ℕ) ≤ ((55721541/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_264 :
    ((5575949/1000000 : ℚ) : ℝ) ≤ Real.log (264 : ℕ)
      ∧ Real.log (264 : ℕ) ≤ ((55759493/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_265 :
    ((27898649/5000000 : ℚ) : ℝ) ≤ Real.log (265 : ℕ)
      ∧ Real.log (265 : ℕ) ≤ ((55797299/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_266 :
    ((55834963/10000000 : ℚ) : ℝ) ≤ Real.log (266 : ℕ)
      ∧ Real.log (266 : ℕ) ≤ ((13958741/2500000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_267 :
    ((27936243/5000000 : ℚ) : ℝ) ≤ Real.log (267 : ℕ)
      ∧ Real.log (267 : ℕ) ≤ ((55872487/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_268 :
    ((55909869/10000000 : ℚ) : ℝ) ≤ Real.log (268 : ℕ)
      ∧ Real.log (268 : ℕ) ≤ ((5590987/1000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_269 :
    ((55947113/10000000 : ℚ) : ℝ) ≤ Real.log (269 : ℕ)
      ∧ Real.log (269 : ℕ) ≤ ((27973557/5000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_270 :
    ((55984219/10000000 : ℚ) : ℝ) ≤ Real.log (270 : ℕ)
      ∧ Real.log (270 : ℕ) ≤ ((2799211/500000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_271 :
    ((14005297/2500000 : ℚ) : ℝ) ≤ Real.log (271 : ℕ)
      ∧ Real.log (271 : ℕ) ≤ ((56021189/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_272 :
    ((2802901/500000 : ℚ) : ℝ) ≤ Real.log (272 : ℕ)
      ∧ Real.log (272 : ℕ) ≤ ((56058021/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_273 :
    ((56094717/10000000 : ℚ) : ℝ) ≤ Real.log (273 : ℕ)
      ∧ Real.log (273 : ℕ) ≤ ((28047359/5000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_274 :
    ((56131281/10000000 : ℚ) : ℝ) ≤ Real.log (274 : ℕ)
      ∧ Real.log (274 : ℕ) ≤ ((28065641/5000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_275 :
    ((5616771/1000000 : ℚ) : ℝ) ≤ Real.log (275 : ℕ)
      ∧ Real.log (275 : ℕ) ≤ ((56167711/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_276 :
    ((7025501/1250000 : ℚ) : ℝ) ≤ Real.log (276 : ℕ)
      ∧ Real.log (276 : ℕ) ≤ ((56204009/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_277 :
    ((2249607/400000 : ℚ) : ℝ) ≤ Real.log (277 : ℕ)
      ∧ Real.log (277 : ℕ) ≤ ((3515011/625000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_278 :
    ((56276211/10000000 : ℚ) : ℝ) ≤ Real.log (278 : ℕ)
      ∧ Real.log (278 : ℕ) ≤ ((14069053/2500000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_279 :
    ((56312117/10000000 : ℚ) : ℝ) ≤ Real.log (279 : ℕ)
      ∧ Real.log (279 : ℕ) ≤ ((28156059/5000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_280 :
    ((7043487/1250000 : ℚ) : ℝ) ≤ Real.log (280 : ℕ)
      ∧ Real.log (280 : ℕ) ≤ ((56347897/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_281 :
    ((28191773/5000000 : ℚ) : ℝ) ≤ Real.log (281 : ℕ)
      ∧ Real.log (281 : ℕ) ≤ ((56383547/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_282 :
    ((5641907/1000000 : ℚ) : ℝ) ≤ Real.log (282 : ℕ)
      ∧ Real.log (282 : ℕ) ≤ ((56419071/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_283 :
    ((14113617/2500000 : ℚ) : ℝ) ≤ Real.log (283 : ℕ)
      ∧ Real.log (283 : ℕ) ≤ ((56454469/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_284 :
    ((28244871/5000000 : ℚ) : ℝ) ≤ Real.log (284 : ℕ)
      ∧ Real.log (284 : ℕ) ≤ ((56489743/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_285 :
    ((56524891/10000000 : ℚ) : ℝ) ≤ Real.log (285 : ℕ)
      ∧ Real.log (285 : ℕ) ≤ ((14131223/2500000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_286 :
    ((28279959/5000000 : ℚ) : ℝ) ≤ Real.log (286 : ℕ)
      ∧ Real.log (286 : ℕ) ≤ ((56559919/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_287 :
    ((28297411/5000000 : ℚ) : ℝ) ≤ Real.log (287 : ℕ)
      ∧ Real.log (287 : ℕ) ≤ ((56594823/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_288 :
    ((14157401/2500000 : ℚ) : ℝ) ≤ Real.log (288 : ℕ)
      ∧ Real.log (288 : ℕ) ≤ ((11325921/2000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_289 :
    ((28332133/5000000 : ℚ) : ℝ) ≤ Real.log (289 : ℕ)
      ∧ Real.log (289 : ℕ) ≤ ((56664267/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_290 :
    ((56698809/10000000 : ℚ) : ℝ) ≤ Real.log (290 : ℕ)
      ∧ Real.log (290 : ℕ) ≤ ((5669881/1000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_291 :
    ((3545827/625000 : ℚ) : ℝ) ≤ Real.log (291 : ℕ)
      ∧ Real.log (291 : ℕ) ≤ ((56733233/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_292 :
    ((28383769/5000000 : ℚ) : ℝ) ≤ Real.log (292 : ℕ)
      ∧ Real.log (292 : ℕ) ≤ ((56767539/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_293 :
    ((28400863/5000000 : ℚ) : ℝ) ≤ Real.log (293 : ℕ)
      ∧ Real.log (293 : ℕ) ≤ ((56801727/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_294 :
    ((56835797/10000000 : ℚ) : ℝ) ≤ Real.log (294 : ℕ)
      ∧ Real.log (294 : ℕ) ≤ ((28417899/5000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_295 :
    ((56869753/10000000 : ℚ) : ℝ) ≤ Real.log (295 : ℕ)
      ∧ Real.log (295 : ℕ) ≤ ((28434877/5000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_296 :
    ((28451797/5000000 : ℚ) : ℝ) ≤ Real.log (296 : ℕ)
      ∧ Real.log (296 : ℕ) ≤ ((11380719/2000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_297 :
    ((56937321/10000000 : ℚ) : ℝ) ≤ Real.log (297 : ℕ)
      ∧ Real.log (297 : ℕ) ≤ ((28468661/5000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_298 :
    ((28485467/5000000 : ℚ) : ℝ) ≤ Real.log (298 : ℕ)
      ∧ Real.log (298 : ℕ) ≤ ((11394187/2000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_299 :
    ((11400887/2000000 : ℚ) : ℝ) ≤ Real.log (299 : ℕ)
      ∧ Real.log (299 : ℕ) ≤ ((14251109/2500000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_300 :
    ((445608/78125 : ℚ) : ℝ) ≤ Real.log (300 : ℕ)
      ∧ Real.log (300 : ℕ) ≤ ((2281513/400000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_301 :
    ((28535551/5000000 : ℚ) : ℝ) ≤ Real.log (301 : ℕ)
      ∧ Real.log (301 : ℕ) ≤ ((57071103/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_302 :
    ((5710427/1000000 : ℚ) : ℝ) ≤ Real.log (302 : ℕ)
      ∧ Real.log (302 : ℕ) ≤ ((57104271/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_303 :
    ((3571083/625000 : ℚ) : ℝ) ≤ Real.log (303 : ℕ)
      ∧ Real.log (303 : ℕ) ≤ ((57137329/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_304 :
    ((57170277/10000000 : ℚ) : ℝ) ≤ Real.log (304 : ℕ)
      ∧ Real.log (304 : ℕ) ≤ ((28585139/5000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_305 :
    ((57203117/10000000 : ℚ) : ℝ) ≤ Real.log (305 : ℕ)
      ∧ Real.log (305 : ℕ) ≤ ((28601559/5000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_306 :
    ((57235851/10000000 : ℚ) : ℝ) ≤ Real.log (306 : ℕ)
      ∧ Real.log (306 : ℕ) ≤ ((14308963/2500000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_307 :
    ((57268477/10000000 : ℚ) : ℝ) ≤ Real.log (307 : ℕ)
      ∧ Real.log (307 : ℕ) ≤ ((28634239/5000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_308 :
    ((57300997/10000000 : ℚ) : ℝ) ≤ Real.log (308 : ℕ)
      ∧ Real.log (308 : ℕ) ≤ ((28650499/5000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_309 :
    ((14333353/2500000 : ℚ) : ℝ) ≤ Real.log (309 : ℕ)
      ∧ Real.log (309 : ℕ) ≤ ((57333413/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_310 :
    ((28682861/5000000 : ℚ) : ℝ) ≤ Real.log (310 : ℕ)
      ∧ Real.log (310 : ℕ) ≤ ((57365723/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_311 :
    ((57397929/10000000 : ℚ) : ℝ) ≤ Real.log (311 : ℕ)
      ∧ Real.log (311 : ℕ) ≤ ((5739793/1000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_312 :
    ((57430031/10000000 : ℚ) : ℝ) ≤ Real.log (312 : ℕ)
      ∧ Real.log (312 : ℕ) ≤ ((3589377/625000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_313 :
    ((57462031/10000000 : ℚ) : ℝ) ≤ Real.log (313 : ℕ)
      ∧ Real.log (313 : ℕ) ≤ ((3591377/625000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_314 :
    ((57493929/10000000 : ℚ) : ℝ) ≤ Real.log (314 : ℕ)
      ∧ Real.log (314 : ℕ) ≤ ((5749393/1000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_315 :
    ((28762863/5000000 : ℚ) : ℝ) ≤ Real.log (315 : ℕ)
      ∧ Real.log (315 : ℕ) ≤ ((57525727/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_316 :
    ((28778711/5000000 : ℚ) : ℝ) ≤ Real.log (316 : ℕ)
      ∧ Real.log (316 : ℕ) ≤ ((57557423/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_317 :
    ((57589017/10000000 : ℚ) : ℝ) ≤ Real.log (317 : ℕ)
      ∧ Real.log (317 : ℕ) ≤ ((28794509/5000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_318 :
    ((57620513/10000000 : ℚ) : ℝ) ≤ Real.log (318 : ℕ)
      ∧ Real.log (318 : ℕ) ≤ ((28810257/5000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_319 :
    ((57651911/10000000 : ℚ) : ℝ) ≤ Real.log (319 : ℕ)
      ∧ Real.log (319 : ℕ) ≤ ((7206489/1250000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_320 :
    ((57683209/10000000 : ℚ) : ℝ) ≤ Real.log (320 : ℕ)
      ∧ Real.log (320 : ℕ) ≤ ((5768321/1000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_321 :
    ((57714411/10000000 : ℚ) : ℝ) ≤ Real.log (321 : ℕ)
      ∧ Real.log (321 : ℕ) ≤ ((14428603/2500000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_322 :
    ((11549103/2000000 : ℚ) : ℝ) ≤ Real.log (322 : ℕ)
      ∧ Real.log (322 : ℕ) ≤ ((14436379/2500000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_323 :
    ((57776523/10000000 : ℚ) : ℝ) ≤ Real.log (323 : ℕ)
      ∧ Real.log (323 : ℕ) ≤ ((14444131/2500000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_324 :
    ((11561487/2000000 : ℚ) : ℝ) ≤ Real.log (324 : ℕ)
      ∧ Real.log (324 : ℕ) ≤ ((14451859/2500000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_325 :
    ((57838251/10000000 : ℚ) : ℝ) ≤ Real.log (325 : ℕ)
      ∧ Real.log (325 : ℕ) ≤ ((14459563/2500000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_326 :
    ((57868973/10000000 : ℚ) : ℝ) ≤ Real.log (326 : ℕ)
      ∧ Real.log (326 : ℕ) ≤ ((28934487/5000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_327 :
    ((57899601/10000000 : ℚ) : ℝ) ≤ Real.log (327 : ℕ)
      ∧ Real.log (327 : ℕ) ≤ ((28949801/5000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_328 :
    ((7241267/1250000 : ℚ) : ℝ) ≤ Real.log (328 : ℕ)
      ∧ Real.log (328 : ℕ) ≤ ((57930137/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_329 :
    ((57960577/10000000 : ℚ) : ℝ) ≤ Real.log (329 : ℕ)
      ∧ Real.log (329 : ℕ) ≤ ((28980289/5000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_330 :
    ((28995463/5000000 : ℚ) : ℝ) ≤ Real.log (330 : ℕ)
      ∧ Real.log (330 : ℕ) ≤ ((57990927/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_331 :
    ((58021183/10000000 : ℚ) : ℝ) ≤ Real.log (331 : ℕ)
      ∧ Real.log (331 : ℕ) ≤ ((906581/156250 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_332 :
    ((58051349/10000000 : ℚ) : ℝ) ≤ Real.log (332 : ℕ)
      ∧ Real.log (332 : ℕ) ≤ ((1161027/200000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_333 :
    ((3630089/625000 : ℚ) : ℝ) ≤ Real.log (333 : ℕ)
      ∧ Real.log (333 : ℕ) ≤ ((2323257/400000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_334 :
    ((58111409/10000000 : ℚ) : ℝ) ≤ Real.log (334 : ℕ)
      ∧ Real.log (334 : ℕ) ≤ ((5811141/1000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_335 :
    ((11628261/2000000 : ℚ) : ℝ) ≤ Real.log (335 : ℕ)
      ∧ Real.log (335 : ℕ) ≤ ((29070653/5000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_336 :
    ((58171111/10000000 : ℚ) : ℝ) ≤ Real.log (336 : ℕ)
      ∧ Real.log (336 : ℕ) ≤ ((7271389/1250000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_337 :
    ((58200829/10000000 : ℚ) : ℝ) ≤ Real.log (337 : ℕ)
      ∧ Real.log (337 : ℕ) ≤ ((5820083/1000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_338 :
    ((29115229/5000000 : ℚ) : ℝ) ≤ Real.log (338 : ℕ)
      ∧ Real.log (338 : ℕ) ≤ ((58230459/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_339 :
    ((58260001/10000000 : ℚ) : ℝ) ≤ Real.log (339 : ℕ)
      ∧ Real.log (339 : ℕ) ≤ ((29130001/5000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_340 :
    ((3643091/625000 : ℚ) : ℝ) ≤ Real.log (340 : ℕ)
      ∧ Real.log (340 : ℕ) ≤ ((58289457/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_341 :
    ((7289853/1250000 : ℚ) : ℝ) ≤ Real.log (341 : ℕ)
      ∧ Real.log (341 : ℕ) ≤ ((2332753/400000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_342 :
    ((58348107/10000000 : ℚ) : ℝ) ≤ Real.log (342 : ℕ)
      ∧ Real.log (342 : ℕ) ≤ ((14587027/2500000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_343 :
    ((7297163/1250000 : ℚ) : ℝ) ≤ Real.log (343 : ℕ)
      ∧ Real.log (343 : ℕ) ≤ ((11675461/2000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_344 :
    ((3650401/625000 : ℚ) : ℝ) ≤ Real.log (344 : ℕ)
      ∧ Real.log (344 : ℕ) ≤ ((58406417/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_345 :
    ((14608861/2500000 : ℚ) : ℝ) ≤ Real.log (345 : ℕ)
      ∧ Real.log (345 : ℕ) ≤ ((11687089/2000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_346 :
    ((58464387/10000000 : ℚ) : ℝ) ≤ Real.log (346 : ℕ)
      ∧ Real.log (346 : ℕ) ≤ ((14616097/2500000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_347 :
    ((58493247/10000000 : ℚ) : ℝ) ≤ Real.log (347 : ℕ)
      ∧ Real.log (347 : ℕ) ≤ ((913957/156250 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_348 :
    ((7315253/1250000 : ℚ) : ℝ) ≤ Real.log (348 : ℕ)
      ∧ Real.log (348 : ℕ) ≤ ((2340881/400000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_349 :
    ((58550719/10000000 : ℚ) : ℝ) ≤ Real.log (349 : ℕ)
      ∧ Real.log (349 : ℕ) ≤ ((182971/31250 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_350 :
    ((58579331/10000000 : ℚ) : ℝ) ≤ Real.log (350 : ℕ)
      ∧ Real.log (350 : ℕ) ≤ ((14644833/2500000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_351 :
    ((29303931/5000000 : ℚ) : ℝ) ≤ Real.log (351 : ℕ)
      ∧ Real.log (351 : ℕ) ≤ ((58607863/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_352 :
    ((58636311/10000000 : ℚ) : ℝ) ≤ Real.log (352 : ℕ)
      ∧ Real.log (352 : ℕ) ≤ ((7329539/1250000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_353 :
    ((1466617/250000 : ℚ) : ℝ) ≤ Real.log (353 : ℕ)
      ∧ Real.log (353 : ℕ) ≤ ((58664681/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_354 :
    ((58692969/10000000 : ℚ) : ℝ) ≤ Real.log (354 : ℕ)
      ∧ Real.log (354 : ℕ) ≤ ((5869297/1000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_355 :
    ((58721177/10000000 : ℚ) : ℝ) ≤ Real.log (355 : ℕ)
      ∧ Real.log (355 : ℕ) ≤ ((29360589/5000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_356 :
    ((58749307/10000000 : ℚ) : ℝ) ≤ Real.log (356 : ℕ)
      ∧ Real.log (356 : ℕ) ≤ ((14687327/2500000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_357 :
    ((58777357/10000000 : ℚ) : ℝ) ≤ Real.log (357 : ℕ)
      ∧ Real.log (357 : ℕ) ≤ ((29388679/5000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_358 :
    ((58805329/10000000 : ℚ) : ℝ) ≤ Real.log (358 : ℕ)
      ∧ Real.log (358 : ℕ) ≤ ((5880533/1000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_359 :
    ((58833223/10000000 : ℚ) : ℝ) ≤ Real.log (359 : ℕ)
      ∧ Real.log (359 : ℕ) ≤ ((7354153/1250000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_360 :
    ((735763/125000 : ℚ) : ℝ) ≤ Real.log (360 : ℕ)
      ∧ Real.log (360 : ℕ) ≤ ((58861041/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_361 :
    ((58888779/10000000 : ℚ) : ℝ) ≤ Real.log (361 : ℕ)
      ∧ Real.log (361 : ℕ) ≤ ((2944439/500000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_362 :
    ((29458221/5000000 : ℚ) : ℝ) ≤ Real.log (362 : ℕ)
      ∧ Real.log (362 : ℕ) ≤ ((58916443/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_363 :
    ((14736007/2500000 : ℚ) : ℝ) ≤ Real.log (363 : ℕ)
      ∧ Real.log (363 : ℕ) ≤ ((58944029/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_364 :
    ((29485769/5000000 : ℚ) : ℝ) ≤ Real.log (364 : ℕ)
      ∧ Real.log (364 : ℕ) ≤ ((58971539/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_365 :
    ((58998973/10000000 : ℚ) : ℝ) ≤ Real.log (365 : ℕ)
      ∧ Real.log (365 : ℕ) ≤ ((29499487/5000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_366 :
    ((59026333/10000000 : ℚ) : ℝ) ≤ Real.log (366 : ℕ)
      ∧ Real.log (366 : ℕ) ≤ ((29513167/5000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_367 :
    ((29526809/5000000 : ℚ) : ℝ) ≤ Real.log (367 : ℕ)
      ∧ Real.log (367 : ℕ) ≤ ((59053619/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_368 :
    ((59080829/10000000 : ℚ) : ℝ) ≤ Real.log (368 : ℕ)
      ∧ Real.log (368 : ℕ) ≤ ((5908083/1000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_369 :
    ((29553983/5000000 : ℚ) : ℝ) ≤ Real.log (369 : ℕ)
      ∧ Real.log (369 : ℕ) ≤ ((59107967/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_370 :
    ((5913503/1000000 : ℚ) : ℝ) ≤ Real.log (370 : ℕ)
      ∧ Real.log (370 : ℕ) ≤ ((59135031/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_371 :
    ((2958101/500000 : ℚ) : ℝ) ≤ Real.log (371 : ℕ)
      ∧ Real.log (371 : ℕ) ≤ ((59162021/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_372 :
    ((29594469/5000000 : ℚ) : ℝ) ≤ Real.log (372 : ℕ)
      ∧ Real.log (372 : ℕ) ≤ ((59188939/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_373 :
    ((7401973/1250000 : ℚ) : ℝ) ≤ Real.log (373 : ℕ)
      ∧ Real.log (373 : ℕ) ≤ ((11843157/2000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_374 :
    ((59242557/10000000 : ℚ) : ℝ) ≤ Real.log (374 : ℕ)
      ∧ Real.log (374 : ℕ) ≤ ((29621279/5000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_375 :
    ((2963463/500000 : ℚ) : ℝ) ≤ Real.log (375 : ℕ)
      ∧ Real.log (375 : ℕ) ≤ ((59269261/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_376 :
    ((59295891/10000000 : ℚ) : ℝ) ≤ Real.log (376 : ℕ)
      ∧ Real.log (376 : ℕ) ≤ ((14823973/2500000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_377 :
    ((59322451/10000000 : ℚ) : ℝ) ≤ Real.log (377 : ℕ)
      ∧ Real.log (377 : ℕ) ≤ ((14830613/2500000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_378 :
    ((59348941/10000000 : ℚ) : ℝ) ≤ Real.log (378 : ℕ)
      ∧ Real.log (378 : ℕ) ≤ ((29674471/5000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_379 :
    ((29687681/5000000 : ℚ) : ℝ) ≤ Real.log (379 : ℕ)
      ∧ Real.log (379 : ℕ) ≤ ((59375363/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_380 :
    ((3712607/625000 : ℚ) : ℝ) ≤ Real.log (380 : ℕ)
      ∧ Real.log (380 : ℕ) ≤ ((59401713/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_381 :
    ((59427993/10000000 : ℚ) : ℝ) ≤ Real.log (381 : ℕ)
      ∧ Real.log (381 : ℕ) ≤ ((29713997/5000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_382 :
    ((29727103/5000000 : ℚ) : ℝ) ≤ Real.log (382 : ℕ)
      ∧ Real.log (382 : ℕ) ≤ ((59454207/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_383 :
    ((59480349/10000000 : ℚ) : ℝ) ≤ Real.log (383 : ℕ)
      ∧ Real.log (383 : ℕ) ≤ ((1189607/200000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_384 :
    ((2380257/400000 : ℚ) : ℝ) ≤ Real.log (384 : ℕ)
      ∧ Real.log (384 : ℕ) ≤ ((29753213/5000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_385 :
    ((59532433/10000000 : ℚ) : ℝ) ≤ Real.log (385 : ℕ)
      ∧ Real.log (385 : ℕ) ≤ ((29766217/5000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_386 :
    ((59558373/10000000 : ℚ) : ℝ) ≤ Real.log (386 : ℕ)
      ∧ Real.log (386 : ℕ) ≤ ((29779187/5000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_387 :
    ((29792123/5000000 : ℚ) : ℝ) ≤ Real.log (387 : ℕ)
      ∧ Real.log (387 : ℕ) ≤ ((59584247/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_388 :
    ((59610053/10000000 : ℚ) : ℝ) ≤ Real.log (388 : ℕ)
      ∧ Real.log (388 : ℕ) ≤ ((29805027/5000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_389 :
    ((59635793/10000000 : ℚ) : ℝ) ≤ Real.log (389 : ℕ)
      ∧ Real.log (389 : ℕ) ≤ ((29817897/5000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_390 :
    ((59661467/10000000 : ℚ) : ℝ) ≤ Real.log (390 : ℕ)
      ∧ Real.log (390 : ℕ) ≤ ((14915367/2500000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_391 :
    ((2387483/400000 : ℚ) : ℝ) ≤ Real.log (391 : ℕ)
      ∧ Real.log (391 : ℕ) ≤ ((14921769/2500000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_392 :
    ((29856309/5000000 : ℚ) : ℝ) ≤ Real.log (392 : ℕ)
      ∧ Real.log (392 : ℕ) ≤ ((59712619/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_393 :
    ((3733631/625000 : ℚ) : ℝ) ≤ Real.log (393 : ℕ)
      ∧ Real.log (393 : ℕ) ≤ ((59738097/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_394 :
    ((59763509/10000000 : ℚ) : ℝ) ≤ Real.log (394 : ℕ)
      ∧ Real.log (394 : ℕ) ≤ ((5976351/1000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_395 :
    ((59788857/10000000 : ℚ) : ℝ) ≤ Real.log (395 : ℕ)
      ∧ Real.log (395 : ℕ) ≤ ((29894429/5000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_396 :
    ((29907071/5000000 : ℚ) : ℝ) ≤ Real.log (396 : ℕ)
      ∧ Real.log (396 : ℕ) ≤ ((59814143/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_397 :
    ((29919681/5000000 : ℚ) : ℝ) ≤ Real.log (397 : ℕ)
      ∧ Real.log (397 : ℕ) ≤ ((59839363/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_398 :
    ((1496613/250000 : ℚ) : ℝ) ≤ Real.log (398 : ℕ)
      ∧ Real.log (398 : ℕ) ≤ ((59864521/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_399 :
    ((29944807/5000000 : ℚ) : ℝ) ≤ Real.log (399 : ℕ)
      ∧ Real.log (399 : ℕ) ≤ ((11977923/2000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_400 :
    ((11982929/2000000 : ℚ) : ℝ) ≤ Real.log (400 : ℕ)
      ∧ Real.log (400 : ℕ) ≤ ((29957323/5000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_401 :
    ((29969807/5000000 : ℚ) : ℝ) ≤ Real.log (401 : ℕ)
      ∧ Real.log (401 : ℕ) ≤ ((11987923/2000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_402 :
    ((1499113/250000 : ℚ) : ℝ) ≤ Real.log (402 : ℕ)
      ∧ Real.log (402 : ℕ) ≤ ((59964521/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_403 :
    ((11997873/2000000 : ℚ) : ℝ) ≤ Real.log (403 : ℕ)
      ∧ Real.log (403 : ℕ) ≤ ((29994683/5000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_404 :
    ((15003537/2500000 : ℚ) : ℝ) ≤ Real.log (404 : ℕ)
      ∧ Real.log (404 : ℕ) ≤ ((60014149/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_405 :
    ((6003887/1000000 : ℚ) : ℝ) ≤ Real.log (405 : ℕ)
      ∧ Real.log (405 : ℕ) ≤ ((60038871/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_406 :
    ((60063531/10000000 : ℚ) : ℝ) ≤ Real.log (406 : ℕ)
      ∧ Real.log (406 : ℕ) ≤ ((15015883/2500000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_407 :
    ((60088131/10000000 : ℚ) : ℝ) ≤ Real.log (407 : ℕ)
      ∧ Real.log (407 : ℕ) ≤ ((15022033/2500000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_408 :
    ((60112671/10000000 : ℚ) : ℝ) ≤ Real.log (408 : ℕ)
      ∧ Real.log (408 : ℕ) ≤ ((1878521/312500 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_409 :
    ((60137151/10000000 : ℚ) : ℝ) ≤ Real.log (409 : ℕ)
      ∧ Real.log (409 : ℕ) ≤ ((939643/156250 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_410 :
    ((60161571/10000000 : ℚ) : ℝ) ≤ Real.log (410 : ℕ)
      ∧ Real.log (410 : ℕ) ≤ ((15040393/2500000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_411 :
    ((15046483/2500000 : ℚ) : ℝ) ≤ Real.log (411 : ℕ)
      ∧ Real.log (411 : ℕ) ≤ ((60185933/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_412 :
    ((60210233/10000000 : ℚ) : ℝ) ≤ Real.log (412 : ℕ)
      ∧ Real.log (412 : ℕ) ≤ ((30105117/5000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_413 :
    ((2409379/400000 : ℚ) : ℝ) ≤ Real.log (413 : ℕ)
      ∧ Real.log (413 : ℕ) ≤ ((15058619/2500000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_414 :
    ((60258659/10000000 : ℚ) : ℝ) ≤ Real.log (414 : ℕ)
      ∧ Real.log (414 : ℕ) ≤ ((3012933/500000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_415 :
    ((12056557/2000000 : ℚ) : ℝ) ≤ Real.log (415 : ℕ)
      ∧ Real.log (415 : ℕ) ≤ ((30141393/5000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_416 :
    ((15076713/2500000 : ℚ) : ℝ) ≤ Real.log (416 : ℕ)
      ∧ Real.log (416 : ℕ) ≤ ((60306853/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_417 :
    ((30165431/5000000 : ℚ) : ℝ) ≤ Real.log (417 : ℕ)
      ∧ Real.log (417 : ℕ) ≤ ((60330863/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_418 :
    ((30177407/5000000 : ℚ) : ℝ) ≤ Real.log (418 : ℕ)
      ∧ Real.log (418 : ℕ) ≤ ((12070963/2000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_419 :
    ((60378709/10000000 : ℚ) : ℝ) ≤ Real.log (419 : ℕ)
      ∧ Real.log (419 : ℕ) ≤ ((6037871/1000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_420 :
    ((60402547/10000000 : ℚ) : ℝ) ≤ Real.log (420 : ℕ)
      ∧ Real.log (420 : ℕ) ≤ ((15100637/2500000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_421 :
    ((7553291/1250000 : ℚ) : ℝ) ≤ Real.log (421 : ℕ)
      ∧ Real.log (421 : ℕ) ≤ ((60426329/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_422 :
    ((60450053/10000000 : ℚ) : ℝ) ≤ Real.log (422 : ℕ)
      ∧ Real.log (422 : ℕ) ≤ ((30225027/5000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_423 :
    ((60473721/10000000 : ℚ) : ℝ) ≤ Real.log (423 : ℕ)
      ∧ Real.log (423 : ℕ) ≤ ((30236861/5000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_424 :
    ((30248667/5000000 : ℚ) : ℝ) ≤ Real.log (424 : ℕ)
      ∧ Real.log (424 : ℕ) ≤ ((12099467/2000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_425 :
    ((60520891/10000000 : ℚ) : ℝ) ≤ Real.log (425 : ℕ)
      ∧ Real.log (425 : ℕ) ≤ ((15130223/2500000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_426 :
    ((60544393/10000000 : ℚ) : ℝ) ≤ Real.log (426 : ℕ)
      ∧ Real.log (426 : ℕ) ≤ ((30272197/5000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_427 :
    ((378549/62500 : ℚ) : ℝ) ≤ Real.log (427 : ℕ)
      ∧ Real.log (427 : ℕ) ≤ ((60567841/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_428 :
    ((60591231/10000000 : ℚ) : ℝ) ≤ Real.log (428 : ℕ)
      ∧ Real.log (428 : ℕ) ≤ ((473369/78125 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_429 :
    ((60614569/10000000 : ℚ) : ℝ) ≤ Real.log (429 : ℕ)
      ∧ Real.log (429 : ℕ) ≤ ((6061457/1000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_430 :
    ((15159463/2500000 : ℚ) : ℝ) ≤ Real.log (430 : ℕ)
      ∧ Real.log (430 : ℕ) ≤ ((60637853/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_431 :
    ((1516527/250000 : ℚ) : ℝ) ≤ Real.log (431 : ℕ)
      ∧ Real.log (431 : ℕ) ≤ ((60661081/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_432 :
    ((12136851/2000000 : ℚ) : ℝ) ≤ Real.log (432 : ℕ)
      ∧ Real.log (432 : ℕ) ≤ ((1896383/312500 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_433 :
    ((60707377/10000000 : ℚ) : ℝ) ≤ Real.log (433 : ℕ)
      ∧ Real.log (433 : ℕ) ≤ ((30353689/5000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_434 :
    ((12146089/2000000 : ℚ) : ℝ) ≤ Real.log (434 : ℕ)
      ∧ Real.log (434 : ℕ) ≤ ((30365223/5000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_435 :
    ((3037673/500000 : ℚ) : ℝ) ≤ Real.log (435 : ℕ)
      ∧ Real.log (435 : ℕ) ≤ ((60753461/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_436 :
    ((30388211/5000000 : ℚ) : ℝ) ≤ Real.log (436 : ℕ)
      ∧ Real.log (436 : ℕ) ≤ ((60776423/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_437 :
    ((60799331/10000000 : ℚ) : ℝ) ≤ Real.log (437 : ℕ)
      ∧ Real.log (437 : ℕ) ≤ ((15199833/2500000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_438 :
    ((60822189/10000000 : ℚ) : ℝ) ≤ Real.log (438 : ℕ)
      ∧ Real.log (438 : ℕ) ≤ ((6082219/1000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_439 :
    ((30422497/5000000 : ℚ) : ℝ) ≤ Real.log (439 : ℕ)
      ∧ Real.log (439 : ℕ) ≤ ((12168999/2000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_440 :
    ((60867747/10000000 : ℚ) : ℝ) ≤ Real.log (440 : ℕ)
      ∧ Real.log (440 : ℕ) ≤ ((15216937/2500000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_441 :
    ((3805653/625000 : ℚ) : ℝ) ≤ Real.log (441 : ℕ)
      ∧ Real.log (441 : ℕ) ≤ ((60890449/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_442 :
    ((30456549/5000000 : ℚ) : ℝ) ≤ Real.log (442 : ℕ)
      ∧ Real.log (442 : ℕ) ≤ ((60913099/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_443 :
    ((60935697/10000000 : ℚ) : ℝ) ≤ Real.log (443 : ℕ)
      ∧ Real.log (443 : ℕ) ≤ ((30467849/5000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_444 :
    ((12191649/2000000 : ℚ) : ℝ) ≤ Real.log (444 : ℕ)
      ∧ Real.log (444 : ℕ) ≤ ((30479123/5000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_445 :
    ((30490371/5000000 : ℚ) : ℝ) ≤ Real.log (445 : ℕ)
      ∧ Real.log (445 : ℕ) ≤ ((60980743/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_446 :
    ((61003189/10000000 : ℚ) : ℝ) ≤ Real.log (446 : ℕ)
      ∧ Real.log (446 : ℕ) ≤ ((6100319/1000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_447 :
    ((12205117/2000000 : ℚ) : ℝ) ≤ Real.log (447 : ℕ)
      ∧ Real.log (447 : ℕ) ≤ ((30512793/5000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_448 :
    ((15261983/2500000 : ℚ) : ℝ) ≤ Real.log (448 : ℕ)
      ∧ Real.log (448 : ℕ) ≤ ((61047933/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_449 :
    ((15267557/2500000 : ℚ) : ℝ) ≤ Real.log (449 : ℕ)
      ∧ Real.log (449 : ℕ) ≤ ((61070229/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_450 :
    ((2443699/400000 : ℚ) : ℝ) ≤ Real.log (450 : ℕ)
      ∧ Real.log (450 : ℕ) ≤ ((15273119/2500000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_451 :
    ((61114673/10000000 : ℚ) : ℝ) ≤ Real.log (451 : ℕ)
      ∧ Real.log (451 : ℕ) ≤ ((30557337/5000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_452 :
    ((61136821/10000000 : ℚ) : ℝ) ≤ Real.log (452 : ℕ)
      ∧ Real.log (452 : ℕ) ≤ ((30568411/5000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_453 :
    ((61158921/10000000 : ℚ) : ℝ) ≤ Real.log (453 : ℕ)
      ∧ Real.log (453 : ℕ) ≤ ((30579461/5000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_454 :
    ((61180971/10000000 : ℚ) : ℝ) ≤ Real.log (454 : ℕ)
      ∧ Real.log (454 : ℕ) ≤ ((15295243/2500000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_455 :
    ((30601487/5000000 : ℚ) : ℝ) ≤ Real.log (455 : ℕ)
      ∧ Real.log (455 : ℕ) ≤ ((2448119/400000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_456 :
    ((1913279/312500 : ℚ) : ℝ) ≤ Real.log (456 : ℕ)
      ∧ Real.log (456 : ℕ) ≤ ((61224929/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_457 :
    ((61246833/10000000 : ℚ) : ℝ) ≤ Real.log (457 : ℕ)
      ∧ Real.log (457 : ℕ) ≤ ((30623417/5000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_458 :
    ((61268691/10000000 : ℚ) : ℝ) ≤ Real.log (458 : ℕ)
      ∧ Real.log (458 : ℕ) ≤ ((15317173/2500000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_459 :
    ((30645251/5000000 : ℚ) : ℝ) ≤ Real.log (459 : ℕ)
      ∧ Real.log (459 : ℕ) ≤ ((61290503/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_460 :
    ((7664033/1250000 : ℚ) : ℝ) ≤ Real.log (460 : ℕ)
      ∧ Real.log (460 : ℕ) ≤ ((12262453/2000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_461 :
    ((3066699/500000 : ℚ) : ℝ) ≤ Real.log (461 : ℕ)
      ∧ Real.log (461 : ℕ) ≤ ((61333981/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_462 :
    ((479341/78125 : ℚ) : ℝ) ≤ Real.log (462 : ℕ)
      ∧ Real.log (462 : ℕ) ≤ ((61355649/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_463 :
    ((6137727/1000000 : ℚ) : ℝ) ≤ Real.log (463 : ℕ)
      ∧ Real.log (463 : ℕ) ≤ ((61377271/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_464 :
    ((12279769/2000000 : ℚ) : ℝ) ≤ Real.log (464 : ℕ)
      ∧ Real.log (464 : ℕ) ≤ ((30699423/5000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_465 :
    ((30710187/5000000 : ℚ) : ℝ) ≤ Real.log (465 : ℕ)
      ∧ Real.log (465 : ℕ) ≤ ((491363/80000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_466 :
    ((960029/156250 : ℚ) : ℝ) ≤ Real.log (466 : ℕ)
      ∧ Real.log (466 : ℕ) ≤ ((61441857/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_467 :
    ((15365823/2500000 : ℚ) : ℝ) ≤ Real.log (467 : ℕ)
      ∧ Real.log (467 : ℕ) ≤ ((61463293/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_468 :
    ((30742341/5000000 : ℚ) : ℝ) ≤ Real.log (468 : ℕ)
      ∧ Real.log (468 : ℕ) ≤ ((61484683/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_469 :
    ((61506027/10000000 : ℚ) : ℝ) ≤ Real.log (469 : ℕ)
      ∧ Real.log (469 : ℕ) ≤ ((15376507/2500000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_470 :
    ((30763663/5000000 : ℚ) : ℝ) ≤ Real.log (470 : ℕ)
      ∧ Real.log (470 : ℕ) ≤ ((61527327/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_471 :
    ((3077429/500000 : ℚ) : ℝ) ≤ Real.log (471 : ℕ)
      ∧ Real.log (471 : ℕ) ≤ ((61548581/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_472 :
    ((61569789/10000000 : ℚ) : ℝ) ≤ Real.log (472 : ℕ)
      ∧ Real.log (472 : ℕ) ≤ ((6156979/1000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_473 :
    ((61590953/10000000 : ℚ) : ℝ) ≤ Real.log (473 : ℕ)
      ∧ Real.log (473 : ℕ) ≤ ((30795477/5000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_474 :
    ((61612073/10000000 : ℚ) : ℝ) ≤ Real.log (474 : ℕ)
      ∧ Real.log (474 : ℕ) ≤ ((30806037/5000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_475 :
    ((15408287/2500000 : ℚ) : ℝ) ≤ Real.log (475 : ℕ)
      ∧ Real.log (475 : ℕ) ≤ ((61633149/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_476 :
    ((30827089/5000000 : ℚ) : ℝ) ≤ Real.log (476 : ℕ)
      ∧ Real.log (476 : ℕ) ≤ ((61654179/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_477 :
    ((15418791/2500000 : ℚ) : ℝ) ≤ Real.log (477 : ℕ)
      ∧ Real.log (477 : ℕ) ≤ ((12335033/2000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_478 :
    ((61696107/10000000 : ℚ) : ℝ) ≤ Real.log (478 : ℕ)
      ∧ Real.log (478 : ℕ) ≤ ((15424027/2500000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_479 :
    ((12343401/2000000 : ℚ) : ℝ) ≤ Real.log (479 : ℕ)
      ∧ Real.log (479 : ℕ) ≤ ((30858503/5000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_480 :
    ((61737861/10000000 : ℚ) : ℝ) ≤ Real.log (480 : ℕ)
      ∧ Real.log (480 : ℕ) ≤ ((30868931/5000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_481 :
    ((3859917/625000 : ℚ) : ℝ) ≤ Real.log (481 : ℕ)
      ∧ Real.log (481 : ℕ) ≤ ((61758673/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_482 :
    ((61779441/10000000 : ℚ) : ℝ) ≤ Real.log (482 : ℕ)
      ∧ Real.log (482 : ℕ) ≤ ((30889721/5000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_483 :
    ((30900083/5000000 : ℚ) : ℝ) ≤ Real.log (483 : ℕ)
      ∧ Real.log (483 : ℕ) ≤ ((61800167/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_484 :
    ((61820849/10000000 : ℚ) : ℝ) ≤ Real.log (484 : ℕ)
      ∧ Real.log (484 : ℕ) ≤ ((1236417/200000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_485 :
    ((3865093/625000 : ℚ) : ℝ) ≤ Real.log (485 : ℕ)
      ∧ Real.log (485 : ℕ) ≤ ((61841489/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_486 :
    ((30931043/5000000 : ℚ) : ℝ) ≤ Real.log (486 : ℕ)
      ∧ Real.log (486 : ℕ) ≤ ((61862087/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_487 :
    ((61882641/10000000 : ℚ) : ℝ) ≤ Real.log (487 : ℕ)
      ∧ Real.log (487 : ℕ) ≤ ((30941321/5000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_488 :
    ((30951577/5000000 : ℚ) : ℝ) ≤ Real.log (488 : ℕ)
      ∧ Real.log (488 : ℕ) ≤ ((12380631/2000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_489 :
    ((7740453/1250000 : ℚ) : ℝ) ≤ Real.log (489 : ℕ)
      ∧ Real.log (489 : ℕ) ≤ ((495389/80000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_490 :
    ((61944053/10000000 : ℚ) : ℝ) ≤ Real.log (490 : ℕ)
      ∧ Real.log (490 : ℕ) ≤ ((30972027/5000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_491 :
    ((61964441/10000000 : ℚ) : ℝ) ≤ Real.log (491 : ℕ)
      ∧ Real.log (491 : ℕ) ≤ ((30982221/5000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_492 :
    ((61984787/10000000 : ℚ) : ℝ) ≤ Real.log (492 : ℕ)
      ∧ Real.log (492 : ℕ) ≤ ((15496197/2500000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_493 :
    ((62005091/10000000 : ℚ) : ℝ) ≤ Real.log (493 : ℕ)
      ∧ Real.log (493 : ℕ) ≤ ((15501273/2500000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_494 :
    ((12405071/2000000 : ℚ) : ℝ) ≤ Real.log (494 : ℕ)
      ∧ Real.log (494 : ℕ) ≤ ((15506339/2500000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_495 :
    ((62045577/10000000 : ℚ) : ℝ) ≤ Real.log (495 : ℕ)
      ∧ Real.log (495 : ℕ) ≤ ((31022789/5000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_496 :
    ((62065759/10000000 : ℚ) : ℝ) ≤ Real.log (496 : ℕ)
      ∧ Real.log (496 : ℕ) ≤ ((387911/62500 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_497 :
    ((620859/100000 : ℚ) : ℝ) ≤ Real.log (497 : ℕ)
      ∧ Real.log (497 : ℕ) ≤ ((62085901/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_498 :
    ((31053/5000 : ℚ) : ℝ) ≤ Real.log (498 : ℕ)
      ∧ Real.log (498 : ℕ) ≤ ((62106001/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_499 :
    ((3106303/500000 : ℚ) : ℝ) ≤ Real.log (499 : ℕ)
      ∧ Real.log (499 : ℕ) ≤ ((62126061/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

theorem log_br_500 :
    ((388413/62500 : ℚ) : ℝ) ≤ Real.log (500 : ℕ)
      ∧ Real.log (500 : ℕ) ≤ ((62146081/10000000 : ℚ) : ℝ) :=
  log_bracket 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])
    (by norm_num [expTaylor, Finset.sum_range_succ])

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.log_br_500
end AxiomAudit
