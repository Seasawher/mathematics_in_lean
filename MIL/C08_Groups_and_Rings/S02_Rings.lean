import Mathlib.RingTheory.Ideal.QuotientOperations
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal
import Mathlib.Analysis.Complex.Polynomial
import Mathlib.Data.ZMod.Quotient
import MIL.Common

noncomputable section

example {R : Type*} [CommRing R] (x y : R) : (x + y) ^ 2 = x ^ 2 + y ^ 2 + 2 * x * y := by ring

example (x y : ℕ) : (x + y) ^ 2 = x ^ 2 + y ^ 2 + 2 * x * y := by ring

example (x : ℤˣ) : x = 1 ∨ x = -1 := Int.units_eq_one_or x

example {M : Type*} [Monoid M] (x : Mˣ) : (x : M) * x⁻¹ = 1 := Units.mul_inv x

example {M : Type*} [Monoid M] : Group Mˣ := inferInstance

example {R S : Type*} [Ring R] [Ring S] (f : R →+* S) (x y : R) :
    f (x + y) = f x + f y := f.map_add x y

example {R S : Type*} [Ring R] [Ring S] (f : R →+* S) : Rˣ →* Sˣ :=
  Units.map f

example {R : Type*} [Ring R] (S : Subring R) : Ring S := inferInstance

example {R : Type*} [CommRing R] (I : Ideal R) : R →+* R ⧸ I :=
  Ideal.Quotient.mk I

example {R : Type*} [CommRing R] {a : R} {I : Ideal R} :
    Ideal.Quotient.mk I a = 0 ↔ a ∈ I :=
  Ideal.Quotient.eq_zero_iff_mem

example {R S : Type*} [CommRing R] [CommRing S] (I : Ideal R) (f : R →+* S)
    (H : I ≤ RingHom.ker f) : R ⧸ I →+* S :=
  Ideal.Quotient.lift I f H

example {R S : Type*} [CommRing R] [CommRing S](f : R →+* S) :
    R ⧸ RingHom.ker f ≃+* f.range :=
  RingHom.quotientKerEquivRange f

section
variable {R : Type*} [CommRing R] {I J : Ideal R}

example : I + J = I ⊔ J := rfl

example {x : R} : x ∈ I + J ↔ ∃ a ∈ I, ∃ b ∈ J, a + b = x := by
  simp [Submodule.mem_sup]

example : I * J ≤ J := Ideal.mul_le_left

example : I * J ≤ I := Ideal.mul_le_right

example : I * J ≤ I ⊓ J := Ideal.mul_le_inf

end

/-- f : R → S が環準同型で f(I) ⊆ J ならば、
商へのリフト R / I → S / J がある -/
example {R S : Type*} [CommRing R] [CommRing S] (I : Ideal R) (J : Ideal S) (f : R →+* S)
    (H : I ≤ Ideal.comap f J) : R ⧸ I →+* S ⧸ J :=
  Ideal.quotientMap J f H

/-- I = J ならば商環が等しい -/
example {R : Type*} [CommRing R] {I J : Ideal R} (h : I = J) : R ⧸ I ≃+* R ⧸ J :=
  Ideal.quotEquivOfEq h

example {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] (f : ι → Ideal R)
    (hf : ∀ i j, i ≠ j → IsCoprime (f i) (f j)) : (R ⧸ ⨅ i, f i) ≃+* Π i, R ⧸ f i :=
  Ideal.quotientInfRingEquivPiQuotient f hf

open BigOperators PiNotation

example {ι : Type*} [Fintype ι] (a : ι → ℕ) (coprime : ∀ i j, i ≠ j → (a i).Coprime (a j)) :
    ZMod (∏ i, a i) ≃+* Π i, ZMod (a i) :=
  ZMod.prodEquivPi a coprime

section
variable {ι R : Type*} [CommRing R]
open Ideal Quotient Function

#check Quotient.lift

#check Pi.ringHom
#check ker_Pi_Quotient_mk

#check InfSet

/-- 中国式剰余定理で登場する同型写像 ``R ⧸ ⨅ i, I i ≃+* Π i, R ⧸ I i`` のこと

The homomorphism from ``R ⧸ ⨅ i, I i`` to ``Π i, R ⧸ I i`` featured in the Chinese
  Remainder Theorem. -/
def chineseMap (I : ι → Ideal R) : (R ⧸ ⨅ i, I i) →+* Π i, R ⧸ I i := by
  -- `R → R / Iᵢ` という自然な写像を束ねて、
  -- 積への写像を作る。
  let f : R →+* Π i, R ⧸ I i := Pi.ringHom fun i ↦ mk (I i)

  -- `f` を使って商からの写像を作る。
  -- TODO: Quotiont.lift が邪魔なので隠したいが…
  apply Ideal.Quotient.lift (⨅ i, I i) f

  intro a ha
  rwa [← @RingHom.mem_ker, ker_Pi_Quotient_mk]

lemma chineseMap_mk (I : ι → Ideal R) (x : R) :
    chineseMap I (Quotient.mk _ x) = fun i : ι ↦ Ideal.Quotient.mk (I i) x := by rfl

lemma chineseMap_mk' (I : ι → Ideal R) (x : R) (i : ι) :
    chineseMap I (mk _ x) i = mk (I i) x := by rfl

-- f : R → S を商 R / I → S に持ち上げて単射になるのは、
-- ker f = I のときに限る。
#check injective_lift_iff

lemma chineseMap_inj (I : ι → Ideal R) : Injective (chineseMap I) := by
  dsimp [chineseMap]
  rw [injective_lift_iff]
  rw [ker_Pi_Quotient_mk]

-- a x + b y = 1 となる a,b が存在するとき、
-- x,y は互いに素である。
#check IsCoprime

-- イデアル I,J が互いに素 <=> I + J = (1)
#check isCoprime_iff_add

-- イデアル I,J が互いに素 <=> 1 = i + j となる i ∈ I, j ∈ J が存在する。
#check isCoprime_iff_exists

-- sup で書き直したやつ
#check isCoprime_iff_sup_eq

-- codisjoint で書き直したやつ
#check isCoprime_iff_codisjoint

-- Finset α は、α の有限部分集合の全体
#check Finset

#check Insert.insert

-- `a ∈ s` ならば、`a ∈ s ∪ {b}` が成り立つ
#check Finset.mem_insert_of_mem

#check Finset.mem_insert_self
#check IsLawfulSingleton

/-- `I ⊆ R` がイデアルで、`J : ι → Ideal R` という `R` のイデアルの族があるとする。
かつ有限集合 `s ⊆ ι` があって `j ∈ s` に対して `Jⱼ` と `I` が互いに素だとする。

このとき、`I` と `⨅ j ∈ s, Jⱼ` も互いに素

### s の有限性が必要であること
`ℤ` において `I := 2 ℤ` として、`s := (奇素数全体)`, `Jₚ := p ℤ` とすると
任意の `j ∈ s` に対して `Jⱼ` と `I` は互いに素だが、共通部分はゼロなので主張は成り立たない。
-/
theorem isCoprime_Inf {I : Ideal R} {J : ι → Ideal R} {s : Finset ι}
    (hf : ∀ j ∈ s, IsCoprime I (J j)) : IsCoprime I (⨅ j ∈ s, J j) := by
  -- 任意の命題が決定可能だという公理を導入する
  classical

  -- Coprime というのを I + J = (1) に変える
  simp_rw [isCoprime_iff_add] at *

  -- 有限集合 `s` のサイズに対する帰納法を使う
  induction s using Finset.induction with
  | empty => simp
  | @insert i s _ hs =>
      rw [Finset.iInf_insert, inf_comm, one_eq_top, eq_top_iff, ← one_eq_top]
      set K := ⨅ j ∈ s, J j
      calc
        1 = I + K := ?step1
        _ = I + K * (I + J i)      := ?step2
        _ = (1 + K) * I + K * J i  := ?step3
        _ ≤ I + K ⊓ J i            := ?step4

      case step1 =>
        symm
        apply hs
        intro j hj
        specialize hf j; simp [hj] at hf
        simp_all only [Submodule.add_eq_sup, one_eq_top]

      case step2 =>
        suffices 1 = I + J i from by
          nth_rw 1 [show K = K * 1 from by simp]
          rw [← this]
        specialize hf i; simp at hf
        simp_all only [Submodule.add_eq_sup, one_eq_top]

      case step3 =>
        have lem : K * (I + J i) = K * I + K * J i := by
          exact LeftDistribClass.left_distrib K I (J i)
        rw [lem]
        replace lem : (1 + K) * I = I + K * I := by
          exact one_add_mul K I
        rw [lem]
        ac_rfl

      -- イデアルが積で閉じていることを利用して包含を示す
      case step4 =>
        have lem : K * J i ≤ K ⊓ J i := by
          exact mul_le_inf
        suffices (1 + K) * I ≤ I from by
          exact add_le_add this lem
        exact mul_le_left

/-- イデアルの有限族 `{ Iᵢ } (i ∈ ι)` に対して、
相異なる添え字に対して `Iᵢ` は互いに素だとする。
このとき、中国式剰余定理が存在を主張している写像 `R / ⨅ i, Iᵢ → ⨅ i, (R / Iᵢ)` が全射 -/
lemma chineseMap_surj [Fintype ι] {I : ι → Ideal R}
    (hI : ∀ i j, i ≠ j → IsCoprime (I i) (I j)) : Surjective (chineseMap I) := by
  classical
  -- 値域から何か元が与えられたとする
  intro g

  -- 各 `R → R / Iᵢ` は全射なので、
  -- 任意の `i : ι` に対して、`g` の射影と一致する元 `f i` を選んでくることができる
  choose f hf using fun i ↦ Ideal.Quotient.mk_surjective (g i)

  -- 任意の `i` に対して、
  -- ある `eᵢ : R` が存在して、`eᵢ in (R / I i) = 1` で、
  -- 他の `j` に対しては `eᵢ in (R / I j) = 0` を満たす
  have key : ∀ i, ∃ e : R, mk (I i) e = 1 ∧ ∀ j, j ≠ i → mk (I j) e = 0 := by
    intro i
    have hI' : ∀ j ∈ ({i} : Finset ι)ᶜ, IsCoprime (I i) (I j) := by
      intro j hj
      specialize hI i j
      apply hI
      simp at hj ⊢
      exact fun a ↦ hj (id (Eq.symm a))
    replace hI' := isCoprime_Inf hI'
    clear * - hI'
    replace hI' : (I i) + (⨅ j ∈ ({i} : Finset ι)ᶜ, I j) = 1 := by
      exact IsCoprime.add_eq hI'
    set K := ⨅ j ∈ ({i} : Finset ι)ᶜ, I j with hK
    replace hI' : ∃ x ∈ I i, ∃ y ∈ K, x + y = 1 := by
      sorry
    sorry
  choose e he using key
  use mk _ (∑ i, f i * e i)
  sorry

noncomputable def chineseIso [Fintype ι] (f : ι → Ideal R)
    (hf : ∀ i j, i ≠ j → IsCoprime (f i) (f j)) : (R ⧸ ⨅ i, f i) ≃+* Π i, R ⧸ f i :=
  { Equiv.ofBijective _ ⟨chineseMap_inj f, chineseMap_surj hf⟩,
    chineseMap f with }

end

example {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (r r' : R) (a : A) :
    (r + r') • a = r • a + r' • a :=
  add_smul r r' a

example {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (r r' : R) (a : A) :
    (r * r') • a = r • r' • a :=
  mul_smul r r' a

section Polynomials
open Polynomial

example {R : Type*} [CommRing R] : R[X] := X

example {R : Type*} [CommRing R] (r : R) := X - C r

example {R : Type*} [CommRing R] (r : R) : (X + C r) * (X - C r) = X ^ 2 - C (r ^ 2) := by
  rw [C.map_pow]
  ring

example {R : Type*} [CommRing R] (r:R) : (C r).coeff 0 = r := by simp

example {R : Type*} [CommRing R] : (X ^ 2 + 2 * X + C 3 : R[X]).coeff 1 = 2 := by simp

example {R : Type*} [Semiring R] [NoZeroDivisors R] {p q : R[X]} :
    degree (p * q) = degree p + degree q :=
  Polynomial.degree_mul

example {R : Type*} [Semiring R] [NoZeroDivisors R] {p q : R[X]} (hp : p ≠ 0) (hq : q ≠ 0) :
    natDegree (p * q) = natDegree p + natDegree q :=
  Polynomial.natDegree_mul hp hq

example {R : Type*} [Semiring R] [NoZeroDivisors R] {p q : R[X]} :
    natDegree (comp p q) = natDegree p * natDegree q :=
  Polynomial.natDegree_comp

example {R : Type*} [CommRing R] (P: R[X]) (x : R) := P.eval x

example {R : Type*} [CommRing R] (r : R) : (X - C r).eval r = 0 := by simp

example {R : Type*} [CommRing R] (P : R[X]) (r : R) : IsRoot P r ↔ P.eval r = 0 := Iff.rfl

example {R : Type*} [CommRing R] [IsDomain R] (r : R) : (X - C r).roots = {r} :=
  roots_X_sub_C r

example {R : Type*} [CommRing R] [IsDomain R] (r : R) (n : ℕ):
    ((X - C r) ^ n).roots = n • {r} :=
  by simp

example : aeval Complex.I (X ^ 2 + 1 : ℝ[X]) = 0 := by simp

open Complex Polynomial

example : aroots (X ^ 2 + 1 : ℝ[X]) ℂ = {Complex.I, -I} := by
  suffices roots (X ^ 2 + 1 : ℂ[X]) = {I, -I} by simpa [aroots_def]
  have factored : (X ^ 2 + 1 : ℂ[X]) = (X - C I) * (X - C (-I)) := by
    rw [C_neg]
    linear_combination show (C I * C I : ℂ[X]) = -1 by simp [← C_mul]
  have p_ne_zero : (X - C I) * (X - C (-I)) ≠ 0 := by
    intro H
    apply_fun eval 0 at H
    simp [eval] at H
  simp only [factored, roots_mul p_ne_zero, roots_X_sub_C]
  rfl

-- Mathlib knows about D'Alembert-Gauss theorem: ``ℂ`` is algebraically closed.
example : IsAlgClosed ℂ := inferInstance

#check (Complex.ofReal : ℝ →+* ℂ)

example : (X ^ 2 + 1 : ℝ[X]).eval₂ Complex.ofReal Complex.I = 0 := by simp

open MvPolynomial

def circleEquation : MvPolynomial (Fin 2) ℝ := X 0 ^ 2 + X 1 ^ 2 - 1

example : MvPolynomial.eval ![0, 1] circleEquation = 0 := by simp [circleEquation]

end Polynomials
