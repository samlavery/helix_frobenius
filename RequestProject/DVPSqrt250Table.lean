import RequestProject.DVPSqrtTable

/-!
# `n^{−1/2}` brackets, `n = 201..250` (rung-109 extension)
-/

noncomputable section

namespace CriticalLinePhasor.DVP

theorem sq_br_201 :
    ((141069/2000000 : ℚ) : ℝ) ≤ ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((352673/5000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_202 :
    ((703597/10000000 : ℚ) : ℝ) ≤ ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((351799/5000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_203 :
    ((350931/5000000 : ℚ) : ℝ) ≤ ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((701863/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_204 :
    ((35007/500000 : ℚ) : ℝ) ≤ ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((700141/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_205 :
    ((69843/1000000 : ℚ) : ℝ) ≤ ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((698431/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_206 :
    ((696733/10000000 : ℚ) : ℝ) ≤ ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((348367/5000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_207 :
    ((86881/1250000 : ℚ) : ℝ) ≤ ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((695049/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_208 :
    ((5547/80000 : ℚ) : ℝ) ≤ ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((5417/78125 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_209 :
    ((345857/5000000 : ℚ) : ℝ) ≤ ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((138343/2000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_210 :
    ((138013/2000000 : ℚ) : ℝ) ≤ ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((345033/5000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_211 :
    ((172107/2500000 : ℚ) : ℝ) ≤ ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((688429/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_212 :
    ((343401/5000000 : ℚ) : ℝ) ≤ ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((686803/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_213 :
    ((171297/2500000 : ℚ) : ℝ) ≤ ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((685189/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_214 :
    ((136717/2000000 : ℚ) : ℝ) ≤ ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((341793/5000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_215 :
    ((340997/5000000 : ℚ) : ℝ) ≤ ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((136399/2000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_216 :
    ((680413/10000000 : ℚ) : ℝ) ≤ ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((340207/5000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_217 :
    ((169711/2500000 : ℚ) : ℝ) ≤ ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((135769/2000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_218 :
    ((135457/2000000 : ℚ) : ℝ) ≤ ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((338643/5000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_219 :
    ((675737/10000000 : ℚ) : ℝ) ≤ ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((337869/5000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_220 :
    ((674199/10000000 : ℚ) : ℝ) ≤ ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((3371/50000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_221 :
    ((21021/312500 : ℚ) : ℝ) ≤ ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((672673/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_222 :
    ((167789/2500000 : ℚ) : ℝ) ≤ ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((671157/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_223 :
    ((669649/10000000 : ℚ) : ℝ) ≤ ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((13393/200000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_224 :
    ((668153/10000000 : ℚ) : ℝ) ≤ ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((334077/5000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_225 :
    ((333333/5000000 : ℚ) : ℝ) ≤ ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((666667/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_226 :
    ((66519/1000000 : ℚ) : ℝ) ≤ ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((665191/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_227 :
    ((663723/10000000 : ℚ) : ℝ) ≤ ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((165931/2500000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_228 :
    ((331133/5000000 : ℚ) : ℝ) ≤ ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((662267/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_229 :
    ((330409/5000000 : ℚ) : ℝ) ≤ ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((660819/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_230 :
    ((32969/500000 : ℚ) : ℝ) ≤ ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((659381/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_231 :
    ((657951/10000000 : ℚ) : ℝ) ≤ ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((20561/312500 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_232 :
    ((164133/2500000 : ℚ) : ℝ) ≤ ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((656533/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_233 :
    ((655121/10000000 : ℚ) : ℝ) ≤ ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((327561/5000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_234 :
    ((16343/250000 : ℚ) : ℝ) ≤ ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((653721/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_235 :
    ((81541/1250000 : ℚ) : ℝ) ≤ ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((652329/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_236 :
    ((10171/156250 : ℚ) : ℝ) ≤ ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((130189/2000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_237 :
    ((649569/10000000 : ℚ) : ℝ) ≤ ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((64957/1000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_238 :
    ((648203/10000000 : ℚ) : ℝ) ≤ ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((162051/2500000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_239 :
    ((323423/5000000 : ℚ) : ℝ) ≤ ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((646847/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_240 :
    ((645497/10000000 : ℚ) : ℝ) ≤ ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((322749/5000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_241 :
    ((161039/2500000 : ℚ) : ℝ) ≤ ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((644157/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_242 :
    ((80353/1250000 : ℚ) : ℝ) ≤ ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((25713/400000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_243 :
    ((1283/20000 : ℚ) : ℝ) ≤ ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((641501/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_244 :
    ((80023/1250000 : ℚ) : ℝ) ≤ ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((128037/2000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_245 :
    ((159719/2500000 : ℚ) : ℝ) ≤ ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((638877/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_246 :
    ((79697/1250000 : ℚ) : ℝ) ≤ ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((637577/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_247 :
    ((159071/2500000 : ℚ) : ℝ) ≤ ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((127257/2000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_248 :
    ((127/2000 : ℚ) : ℝ) ≤ ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((635001/10000000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_249 :
    ((158431/2500000 : ℚ) : ℝ) ≤ ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((25349/400000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem sq_br_250 :
    ((126491/2000000 : ℚ) : ℝ) ≤ ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
      ∧ ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ ((79057/1250000 : ℚ) : ℝ) :=
  inv_sqrt_enclosure (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.sq_br_250
end AxiomAudit
