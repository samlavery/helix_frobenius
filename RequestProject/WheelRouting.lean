import Mathlib
import RequestProject.HelixEmpiricalCores

/-!
# The wheel routing core (ledger 1141)

The routing of a phasor into a bank, separated from any fiber so that the grown fiber can take it
as a parameter (`GrownFiberEvolution.routedGrownFiber`). Moved here from `EisensteinWheelBank`.

* The exact Eisenstein wheel: `Eisenstein` (`a + b·ζ`, `ζ = e^{iπ/3}`, `ζ² = ζ − 1`;
  carrier_fiber.py `class Eisenstein`), `zeta6Powers` (`ZETA6_POWERS`), and its complex point
  `Eisenstein.toComplex` through the compiled `HelixEmpiricalCores.eisensteinOmega`.
* The generator walk of `focal_closure.character_values(q, gen, order)`: `stepTuples`,
  `walkResidue`, `walkSteps` (`none` when the walk never reaches the site), `walkPos` (six-cell
  position), `walkValueC` (complex value, any order).
* `Routing`: `eta` for the trivial function, `walk q order gens strides` for a conductor walk of
  the given order. `Routing.coeff` is the complex routed coefficient: the wheel state stays complex
  until a fiber consumes it. `Routing.pos` and `Routing.value` are the exact six-cell readings,
  equal to the coefficient whenever the order divides 6 (`coeff_walk_eq_toComplex_value`).
-/

namespace CriticalLinePhasor.EisensteinWheelBank

/-! ## The exact Eisenstein wheel -/

/-- `class Eisenstein` (carrier_fiber.py:301): exact `a + b·ζ` with `ζ = exp(iπ/3)`, `ζ² = ζ − 1`. -/
@[ext] structure Eisenstein where
  a : ℤ
  b : ℤ
  deriving DecidableEq, Repr

namespace Eisenstein

/-- `Eisenstein()`: the zero marker. -/
instance : Zero Eisenstein := ⟨⟨0, 0⟩⟩

/-- `__add__`. -/
instance : Add Eisenstein := ⟨fun x y => ⟨x.a + y.a, x.b + y.b⟩⟩

/-- `__neg__`. -/
instance : Neg Eisenstein := ⟨fun x => ⟨-x.a, -x.b⟩⟩

/-- `__mul__`: `(a+bζ)(c+dζ) = ac + (ad+bc)ζ + bd ζ²`, `ζ² = ζ − 1`. -/
instance : Mul Eisenstein :=
  ⟨fun x y => ⟨x.a * y.a - x.b * y.b, x.a * y.b + x.b * y.a + x.b * y.b⟩⟩

/-- `scale(k)`. -/
def scale (k : ℤ) (x : Eisenstein) : Eisenstein := ⟨k * x.a, k * x.b⟩

/-- `is_zero()`. -/
def IsZero (x : Eisenstein) : Prop := x.a = 0 ∧ x.b = 0

end Eisenstein

/-- `ZETA6_POWERS` (carrier_fiber.py:327): `ζ^0, …, ζ^5` in the basis `(1, ζ)`. -/
def zeta6Powers : Fin 6 → Eisenstein :=
  ![⟨1, 0⟩, ⟨0, 1⟩, ⟨-1, 1⟩, ⟨-1, 0⟩, ⟨0, -1⟩, ⟨1, -1⟩]

/-- The table is the successive powers of `ζ`: each entry times `ζ` is the next, cyclically. -/
theorem zeta6Powers_succ (j : Fin 6) :
    zeta6Powers j * zeta6Powers 1 = zeta6Powers (j + 1) := by
  fin_cases j <;> decide

open HelixEmpiricalCores in
/-- The complex point of a wheel state: `a + b·ω`, `ω = eisensteinOmega = e^{iπ/3}`. -/
noncomputable def Eisenstein.toComplex (x : Eisenstein) : ℂ := x.a + x.b * eisensteinOmega

theorem Eisenstein.toComplex_zero : (0 : Eisenstein).toComplex = 0 := by
  show ((0 : ℤ) : ℂ) + ((0 : ℤ) : ℂ) * HelixEmpiricalCores.eisensteinOmega = 0
  simp

open HelixEmpiricalCores in
theorem eisensteinOmega_sq : eisensteinOmega ^ 2 = eisensteinOmega - 1 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  apply Complex.ext <;> simp [eisensteinOmega, sq, Complex.mul_re, Complex.mul_im] <;> nlinarith [h3]

theorem Eisenstein.toComplex_mul (x y : Eisenstein) :
    (x * y).toComplex = x.toComplex * y.toComplex := by
  have hω := eisensteinOmega_sq
  show (((x.a * y.a - x.b * y.b : ℤ) : ℂ) +
      ((x.a * y.b + x.b * y.a + x.b * y.b : ℤ) : ℂ) * HelixEmpiricalCores.eisensteinOmega) =
    ((x.a : ℂ) + x.b * HelixEmpiricalCores.eisensteinOmega) *
      ((y.a : ℂ) + y.b * HelixEmpiricalCores.eisensteinOmega)
  push_cast
  linear_combination (-(x.b : ℂ) * y.b) * hω

theorem eisensteinOmega_eq_exp :
    HelixEmpiricalCores.eisensteinOmega = Complex.exp (((Real.pi / 3 : ℝ) : ℂ) * Complex.I) := by
  apply Complex.ext
  · rw [Complex.exp_ofReal_mul_I_re, Real.cos_pi_div_three]
    simp [HelixEmpiricalCores.eisensteinOmega]
  · rw [Complex.exp_ofReal_mul_I_im, Real.sin_pi_div_three]
    simp [HelixEmpiricalCores.eisensteinOmega]

theorem eisensteinOmega_pow_three : HelixEmpiricalCores.eisensteinOmega ^ 3 = -1 := by
  linear_combination (HelixEmpiricalCores.eisensteinOmega + 1) * eisensteinOmega_sq

theorem eisensteinOmega_pow_six : HelixEmpiricalCores.eisensteinOmega ^ 6 = 1 := by
  rw [show (6 : ℕ) = 3 * 2 by norm_num, pow_mul, eisensteinOmega_pow_three]
  norm_num

theorem toComplex_zeta6Powers (j : Fin 6) :
    (zeta6Powers j).toComplex = HelixEmpiricalCores.eisensteinOmega ^ (j : ℕ) := by
  have hω := eisensteinOmega_sq
  have h3 := eisensteinOmega_pow_three
  fin_cases j <;> simp [zeta6Powers, Eisenstein.toComplex]
  · linear_combination (-1 : ℂ) * hω
  · linear_combination (-1 : ℂ) * h3
  · linear_combination (-HelixEmpiricalCores.eisensteinOmega) * h3
  · linear_combination (-HelixEmpiricalCores.eisensteinOmega ^ 2) * h3 + hω

/-! ## The generator walk -/

/-- All step tuples `(k₁, …, k_m)` with each `kᵢ < q`. -/
def stepTuples (q : ℕ) : ℕ → List (List ℕ)
  | 0 => [[]]
  | m + 1 => (List.range q).flatMap (fun k => (stepTuples q m).map (k :: ·))

theorem length_of_mem_stepTuples {q : ℕ} :
    ∀ {m : ℕ} {ks : List ℕ}, ks ∈ stepTuples q m → ks.length = m
  | 0, ks, h => by
    simp only [stepTuples, List.mem_singleton] at h
    simp [h]
  | m + 1, ks, h => by
    simp only [stepTuples, List.mem_flatMap, List.mem_map] at h
    obtain ⟨_, _, ks', hks', rfl⟩ := h
    simp [length_of_mem_stepTuples hks']

/-- The residue reached by taking `kᵢ` steps of generator `gᵢ`. -/
def walkResidue (q : ℕ) (gens ks : List ℕ) : ℕ :=
  (List.zipWith (fun g k => g ^ k) gens ks).prod % q

/-- The first step tuple whose walk reaches `n` mod `q`; `none` if the walk never reaches it. -/
def walkSteps (q : ℕ) (gens : List ℕ) (n : ℕ) : Option (List ℕ) :=
  (stepTuples q gens.length).find? (fun ks => walkResidue q gens ks == n % q)

/-- The six-cell wheel position reached: strides times steps, in π/3 cells. -/
def walkPos (q : ℕ) (gens strides : List ℕ) (n : ℕ) : Option (Fin 6) :=
  (walkSteps q gens n).map
    (fun ks => ⟨(List.zipWith (· * ·) strides ks).sum % 6, Nat.mod_lt _ (by norm_num)⟩)

/-- The complex wheel, any order: `exp(2πi · (strides·steps) / order)`, `0` if unreached. -/
noncomputable def walkValueC (q order : ℕ) (gens strides : List ℕ) (n : ℕ) : ℂ :=
  match walkSteps q gens n with
  | none => 0
  | some ks => Complex.exp (2 * Real.pi * Complex.I *
      (((List.zipWith (· * ·) strides ks).sum : ℕ) : ℂ) / order)

theorem walkSteps_mod (q : ℕ) (gens : List ℕ) (n : ℕ) :
    walkSteps q gens (n % q) = walkSteps q gens n := by
  unfold walkSteps
  simp only [Nat.mod_mod]

theorem walkPos_mod (q : ℕ) (gens strides : List ℕ) (n : ℕ) :
    walkPos q gens strides (n % q) = walkPos q gens strides n := by
  unfold walkPos
  rw [walkSteps_mod]

theorem sum_zipWith_map_mul (c : ℕ) : ∀ (strides ks : List ℕ),
    (List.zipWith (· * ·) (strides.map (· * c)) ks).sum =
      c * (List.zipWith (· * ·) strides ks).sum
  | [], _ => by simp
  | _ :: _, [] => by simp
  | st :: strides, k :: ks => by
    simp only [List.map_cons, List.zipWith_cons_cons, List.sum_cons,
      sum_zipWith_map_mul c strides ks]
    ring

/-! ## Routing -/

/-- Which mechanism routes a function: η for the trivial function, a conductor walk of the given
order otherwise. -/
inductive Routing
  | eta
  | walk (q order : ℕ) (gens strides : List ℕ)

/-- η's six-cell position at site `n`: a half-turn per site; position 0 at odd `n`, 3 at even. -/
def etaPos (n : ℕ) : Fin 6 := ⟨(3 * (n + 1)) % 6, Nat.mod_lt _ (by norm_num)⟩

/-- The six-cell wheel position of site `n` (`none` = neutral). A walk's strides are counted in
units of its order; on the six-cell wheel each unit is `6 / order` cells (exact when the order
divides 6). -/
def Routing.pos : Routing → ℕ → Option (Fin 6)
  | .eta, n => some (etaPos n)
  | .walk q order gens strides, n => walkPos q gens (strides.map (· * (6 / order))) n

/-- The exact wheel value of site `n` in `ℤ[ζ₆]`. -/
def Routing.value (r : Routing) (n : ℕ) : Eisenstein :=
  match r.pos n with
  | none => 0
  | some j => zeta6Powers j

/-- The complex routed coefficient of site `n`: η through its six-cell position; a walk through
the complex wheel of its order. -/
noncomputable def Routing.coeff : Routing → ℕ → ℂ
  | .eta, n => (zeta6Powers (etaPos n)).toComplex
  | .walk q order gens strides, n => walkValueC q order gens strides n

theorem coeff_eta_eq_value (n : ℕ) : Routing.eta.coeff n = (Routing.eta.value n).toComplex := rfl

/-- η's routed coefficient at site `k` (phasor `k + 1`) is `(−1)^k`. -/
theorem coeff_eta (k : ℕ) : Routing.eta.coeff (k + 1) = (-1 : ℂ) ^ k := by
  rcases Nat.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · have hp : etaPos (m + m + 1) = 0 :=
      Fin.ext (by show (3 * (m + m + 1 + 1)) % 6 = 0; omega)
    show (zeta6Powers (etaPos (m + m + 1))).toComplex = _
    rw [hp, toComplex_zeta6Powers, Even.neg_one_pow ⟨m, rfl⟩]
    simp
  · have hp : etaPos (2 * m + 1 + 1) = 3 :=
      Fin.ext (by show (3 * (2 * m + 1 + 1 + 1)) % 6 = 3; omega)
    show (zeta6Powers (etaPos (2 * m + 1 + 1))).toComplex = _
    rw [hp, toComplex_zeta6Powers, Odd.neg_one_pow ⟨m, rfl⟩]
    exact eisensteinOmega_pow_three

/-- **At an order dividing 6 the complex coefficient is the exact six-cell value**, at every site,
for every conductor walk. -/
theorem coeff_walk_eq_toComplex_value (q d : ℕ) (gens strides : List ℕ) (hd : d ∣ 6) (n : ℕ) :
    (Routing.walk q d gens strides).coeff n =
      ((Routing.walk q d gens strides).value n).toComplex := by
  have hd0 : d ≠ 0 := by
    rintro rfl
    norm_num at hd
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd0
  show walkValueC q d gens strides n = _
  unfold walkValueC Routing.value Routing.pos walkPos
  rcases h : walkSteps q gens n with _ | ks
  · simp only [h, Option.map_none]
    exact Eisenstein.toComplex_zero.symm
  · simp only [h, Option.map_some]
    rw [toComplex_zeta6Powers]
    simp only
    rw [sum_zipWith_map_mul]
    set S := (List.zipWith (· * ·) strides ks).sum
    have hS : HelixEmpiricalCores.eisensteinOmega ^ ((6 / d * S) % 6) =
        HelixEmpiricalCores.eisensteinOmega ^ (6 / d * S) := by
      conv_rhs => rw [← Nat.div_add_mod (6 / d * S) 6, pow_add, pow_mul, eisensteinOmega_pow_six,
        one_pow, one_mul]
    show Complex.exp (2 * Real.pi * Complex.I * ((S : ℕ) : ℂ) / ((d : ℕ) : ℂ)) =
      HelixEmpiricalCores.eisensteinOmega ^ ((6 / d * S) % 6)
    rw [hS, eisensteinOmega_eq_exp, ← Complex.exp_nat_mul]
    congr 1
    have hcast : ((6 / d : ℕ) : ℂ) = 6 / (d : ℂ) := by
      rw [Nat.cast_div hd hdC]
      norm_num
    rw [Nat.cast_mul, hcast]
    push_cast
    field_simp
    ring

end CriticalLinePhasor.EisensteinWheelBank

#print axioms CriticalLinePhasor.EisensteinWheelBank.zeta6Powers_succ
#print axioms CriticalLinePhasor.EisensteinWheelBank.toComplex_zeta6Powers
#print axioms CriticalLinePhasor.EisensteinWheelBank.coeff_eta
#print axioms CriticalLinePhasor.EisensteinWheelBank.coeff_walk_eq_toComplex_value
