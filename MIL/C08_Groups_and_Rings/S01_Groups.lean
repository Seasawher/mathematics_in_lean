import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.GroupTheory.Perm.Subgroup
import Mathlib.GroupTheory.PresentedGroup

import MIL.Common

example {M : Type*} [Monoid M] (x : M) : x * 1 = x := mul_one x

example {M : Type*} [AddCommMonoid M] (x y : M) : x + y = y + x := add_comm x y

example {M N : Type*} [Monoid M] [Monoid N] (x y : M) (f : M →* N) : f (x * y) = f x * f y :=
  f.map_mul x y

example {M N : Type*} [AddMonoid M] [AddMonoid N] (f : M →+ N) : f 0 = 0 :=
  f.map_zero

example {M N P : Type*} [AddMonoid M] [AddMonoid N] [AddMonoid P]
    (f : M →+ N) (g : N →+ P) : M →+ P := g.comp f

example {G : Type*} [Group G] (x : G) : x * x⁻¹ = 1 := mul_inv_self x

example {G : Type*} [Group G] (x y z : G) : x * (y * z) * (x * z)⁻¹ * (x * y * x⁻¹)⁻¹ = 1 := by
  group

example {G : Type*} [AddCommGroup G] (x y z : G) : z + x + (y - z - x) = y := by
  abel

example {G H : Type*} [Group G] [Group H] (x y : G) (f : G →* H) : f (x * y) = f x * f y :=
  f.map_mul x y

example {G H : Type*} [Group G] [Group H] (x : G) (f : G →* H) : f (x⁻¹) = (f x)⁻¹ :=
  f.map_inv x

example {G H : Type*} [Group G] [Group H] (f : G → H) (h : ∀ x y, f (x * y) = f x * f y) :
    G →* H :=
  MonoidHom.mk' f h

example {G H : Type*} [Group G] [Group H] (f : G ≃* H) :
    f.trans f.symm = MulEquiv.refl G :=
  f.self_trans_symm

noncomputable example {G H : Type*} [Group G] [Group H]
    (f : G →* H) (h : Function.Bijective f) :
    G ≃* H :=
  MulEquiv.ofBijective f h

example {G : Type*} [Group G] (H : Subgroup G) {x y : G} (hx : x ∈ H) (hy : y ∈ H) :
    x * y ∈ H :=
  H.mul_mem hx hy

example {G : Type*} [Group G] (H : Subgroup G) {x : G} (hx : x ∈ H) :
    x⁻¹ ∈ H :=
  H.inv_mem hx

example : AddSubgroup ℚ where
  carrier := Set.range ((↑) : ℤ → ℚ)
  add_mem' := by
    rintro _ _ ⟨n, rfl⟩ ⟨m, rfl⟩
    use n + m
    simp
  zero_mem' := by
    use 0
    simp
  neg_mem' := by
    rintro _ ⟨n, rfl⟩
    use -n
    simp

example {G : Type*} [Group G] (H : Subgroup G) : Group H := inferInstance

example {G : Type*} [Group G] (H : Subgroup G) : Group {x : G // x ∈ H} := inferInstance

example {G : Type*} [Group G] (H H' : Subgroup G) :
    ((H ⊓ H' : Subgroup G) : Set G) = (H : Set G) ∩ (H' : Set G) := rfl

example {G : Type*} [Group G] (H H' : Subgroup G) :
    ((H ⊔ H' : Subgroup G) : Set G) = Subgroup.closure ((H : Set G) ∪ (H' : Set G)) := by
  rw [Subgroup.sup_eq_closure]

example {G : Type*} [Group G] (x : G) : x ∈ (⊤ : Subgroup G) := trivial

example {G : Type*} [Group G] (x : G) : x ∈ (⊥ : Subgroup G) ↔ x = 1 := Subgroup.mem_bot

/-- 部分群 `H ⊆ G` の `x ∈ G` による共役 `x H x⁻¹` -/
def conjugate {G : Type*} [Group G] (x : G) (H : Subgroup G) : Subgroup G where
  carrier := {a : G | ∃ h, h ∈ H ∧ a = x * h * x⁻¹}

  -- 単位元を含む
  one_mem' := by
    dsimp
    use 1
    constructor
    · exact Subgroup.one_mem H
    · group

  -- 逆元に対して閉じている
  inv_mem' := by
    dsimp
    intro y hy
    obtain ⟨h, hmem, hy⟩ := hy
    use h⁻¹
    constructor
    · exact (Subgroup.inv_mem_iff H).mpr hmem
    · rw [hy]
      group

  -- 積を取る操作に対して閉じている
  mul_mem' := by
    dsimp
    intro a b ⟨h, hmem, ha⟩ ⟨g, gmem, ga⟩
    use h * g
    constructor
    · exact (Subgroup.mul_mem_cancel_right H gmem).mpr hmem
    · rw [ha, ga]
      group

example {G H : Type*} [Group G] [Group H] (G' : Subgroup G) (f : G →* H) : Subgroup H :=
  Subgroup.map f G'

example {G H : Type*} [Group G] [Group H] (H' : Subgroup H) (f : G →* H) : Subgroup G :=
  Subgroup.comap f H'

#check Subgroup.mem_map
#check Subgroup.mem_comap

example {G H : Type*} [Group G] [Group H] (f : G →* H) (g : G) :
    g ∈ MonoidHom.ker f ↔ f g = 1 :=
  f.mem_ker

example {G H : Type*} [Group G] [Group H] (f : G →* H) (h : H) :
    h ∈ MonoidHom.range f ↔ ∃ g : G, f g = h :=
  f.mem_range

section exercises
variable {G H : Type*} [Group G] [Group H]

open Subgroup

#synth Preorder (Subgroup G)
#whnf (inferInstance : PartialOrder (Subgroup G))
#synth (PartialOrder (Subgroup G))
#synth (OmegaCompletePartialOrder (Subgroup G))
#synth (CompleteLattice (Subgroup G))
#whnf (inferInstance : CompleteLattice (Subgroup G))

example (φ : G →* H) (S T : Subgroup H) (hST : S ≤ T) : comap φ S ≤ comap φ T := by
  intro g hg
  simp [Subgroup.mem_comap] at hg ⊢
  exact hST hg

example (φ : G →* H) (S T : Subgroup G) (hST : S ≤ T) : map φ S ≤ map φ T := by
  intro h hh
  simp [Subgroup.mem_map] at hh ⊢
  obtain ⟨s, smem, sh⟩ := hh
  use s
  constructor
  · exact hST smem
  · assumption

variable {K : Type*} [Group K]

-- Remember you can use the `ext` tactic to prove an equality of subgroups.
example (φ : G →* H) (ψ : H →* K) (U : Subgroup K) :
    comap (ψ.comp φ) U = comap φ (comap ψ U) := by
  ext x
  simp [Subgroup.mem_comap]

-- Pushing a subgroup along one homomorphism and then another is equal to
-- pushing it forward along the composite of the homomorphisms.
-- S ⊆ G に対して
-- ψ(φ(S)) = (ψ ∘ φ)(S)
example (φ : G →* H) (ψ : H →* K) (S : Subgroup G) :
    map (ψ.comp φ) S = map ψ (S.map φ) := by
  ext x
  simp [Subgroup.mem_map]

end exercises

open scoped Classical

open Fintype

example {G : Type*} [Group G] [Fintype G] (G' : Subgroup G) : card G' ∣ card G :=
  ⟨G'.index, mul_comm G'.index _ ▸ G'.index_mul_card.symm⟩

open Subgroup

example {G : Type*} [Group G] [Fintype G] (p : ℕ) {n : ℕ} [Fact p.Prime]
    (hdvd : p ^ n ∣ card G) : ∃ K : Subgroup G, card K = p ^ n :=
  Sylow.exists_subgroup_card_pow_prime p hdvd

-- 自明な部分群であることと、要素数が１であることが同値
lemma eq_bot_iff_card {G : Type*} [Group G] {H : Subgroup G} [Fintype H] :
    H = ⊥ ↔ card H = 1 := by
  suffices (∀ x ∈ H, x = 1) ↔ ∃ x ∈ H, ∀ a ∈ H, a = x by
    simpa [eq_bot_iff_forall, card_eq_one_iff]
  constructor <;> intro h
  · use 1
    exact ⟨Subgroup.one_mem H, h⟩
  · obtain ⟨x, _xmem, hx⟩ := h
    intro y ymem
    have := Subgroup.one_mem H
    replace : 1 = x := by exact hx 1 this
    rw [← this] at hx
    exact hx y ymem

-- ラグランジュの定理
#check card_dvd_of_le

-- |H| と |K| が互いに素ならば、H ∩ K = {1}
lemma inf_bot_of_coprime {G : Type*} [Group G] (H K : Subgroup G) [Fintype H] [Fintype K]
    (h : (card H).Coprime (card K)) : H ⊓ K = ⊥ := by
  rw [eq_bot_iff_card (H ⊓ K)]
  have left : H ⊓ K ≤ H := inf_le_left
  have right: H ⊓ K ≤ K := inf_le_right
  replace left := card_dvd_of_le left
  replace right := card_dvd_of_le right
  exact Nat.eq_one_of_dvd_coprimes h left right

open Equiv

example {X : Type*} [Finite X] : Subgroup.closure {σ : Perm X | Perm.IsCycle σ} = ⊤ :=
  Perm.closure_isCycle

#simp [mul_assoc] c[1, 2, 3] * c[2, 3, 4]

section FreeGroup

-- S = {a, b, c}
inductive S | a | b | c

open S

-- FreeGroup S := S で生成される自由群
--             = {1, a, b, c, ab, ac, b^2, a^2 b, a b c a b c⁻¹, a b⁻¹, ...}
-- 任意の群は、自由群の剰余群として表現できる

def myElement : FreeGroup S := (.of a) * (.of b)⁻¹

-- α : 集合, β : 群
-- FreeGroup : 集合全体 Type → 群全体 Group
-- Forget : 群全体 Group → 集合全体 Type
--
-- 1. 関数 f : α → Forget β
-- 2. 群準同型 φ : FreeGroup α → β
-- この２つの間に対応をつけることができる
/-
FreeGroup.lift.{u, v} {α : Type u} {β : Type v} [Group β] : (α → β) ≃ (FreeGroup α →* β)
-/
#check FreeGroup.lift

def myMorphism : FreeGroup S →* Perm (Fin 5) :=
  FreeGroup.lift fun | .a => c[1, 2, 3]
                     | .b => c[2, 3, 1]
                     | .c => c[2, 3]

#check myMorphism myElement

-- 値は単位元で、eval するとゼロになる
#eval myMorphism myElement

-- Group でも deriving できる！？
/-- ℤ / 3 ℤ -/
def myGroup := PresentedGroup {.of () ^ 3}

instance : Group myGroup := by
  simp [myGroup]
  infer_instance

/-- 1 の行先だけ決めればいいので myMap : ℤ → Perm (Fin 5) だと見なせる -/
def myMap : Unit → Perm (Fin 5)
| () => c[1, 2, 3]

/-- (1 2 3) という置換を x³ からなる式に代入すると 1 -/
lemma compat_myMap :
    ∀ r ∈ ({.of () ^ 3} : Set (FreeGroup Unit)), FreeGroup.lift myMap r = 1 := by
  rintro _ rfl
  simp
  decide

-- myMap が 3 ℤ の部分をつぶすので、商群の定義より
-- myMap : ℤ → Perm (Fin 5) から ℤ / 3 ℤ →* Perm (Fin 5) という準同型が得られる
-- ℤ --→ Perm (Fin 5)
-- ↓      ↑
-- ℤ / 3 ℤ
def myNewMorphism : myGroup →* Perm (Fin 5) := PresentedGroup.toGroup compat_myMap

end FreeGroup

noncomputable section GroupActions

-- 群 G があって、
-- 群の作用 G × X → X がある
example {G X : Type*} [Group G] [MulAction G X] (g g': G) (x : X) :
    g • (g' • x) = (g * g') • x :=
  (mul_smul g g' x).symm

-- なんで v なんですか？？？
example {G X : Type*} [AddGroup G] [AddAction G X] (g g' : G) (x : X) :
    g +ᵥ (g' +ᵥ x) = (g + g') +ᵥ x :=
  (add_vadd g g' x).symm

open MulAction

-- Equiv.Per X は X 上の全単射がなす群
-- g ∈ G を、(g • ·) : X → X に対応させる。
-- G は群なので可逆で、全単射になってる。
example {G X : Type*} [Group G] [MulAction G X] : G →* Equiv.Perm X :=
  toPermHom G X

-- Cayley の定理で出てくる奴
-- 任意の群 G は、置換群に埋め込めるという定理があって、そこで出てくる同型。
-- G → Equiv.Perm G という上で定義した準同型があるが、これが単射なので。
def CayleyIsoMorphism (G : Type*) [Group G] : G ≃* (toPermHom G G).range :=
  Equiv.Perm.subgroupOfMulAction G G

-- G が集合 X に作用しているときに、x ∈ X が与えられたときに、
-- { g • x | g ∈ G} という集合が考えられて、これが x ∈ X のGによる軌道(orbit)と呼ばれる。
--
-- 集合 X 上の２項関係を「x ∼ y ↔ x と y の軌道が同じ」と定義するとこれは同値関係になっていて、
-- これが多分 orbitRel。
-- 定理の主張は、集合Xと X/∼G × orbit の間に全単射があるというもの
example {G X : Type*} [Group G] [MulAction G X] :
    X ≃ (ω : orbitRel.Quotient G X) × (orbit G (Quotient.out' ω)) :=
  MulAction.selfEquivSigmaOrbits G X

-- 上とほぼ同じ主張だと思われる。
-- 左辺は、x ∈ X の G による軌道
-- 右辺は、x ∈ X の安定化群
--   ただし、x ∈ X の安定化群とは、x に作用しても変わらない g ∈ G の集合
--   g • x = x となる g ∈ G の集合
-- 定理の主張：
--   左辺と右辺の間に全単射がある
--
-- G → orbit G x のつぶれる部分が安定化群なので
example {G X : Type*} [Group G] [MulAction G X] (x : X) :
    orbit G x ≃ G ⧸ stabilizer G x :=
  MulAction.orbitEquivQuotientStabilizer G x

-- 同型にならない例
-- ℤ と ℤ / 2 ℤ ⊕ 2 ℤ は同型にならない
example {G : Type*} [Group G] (H : Subgroup G) : G ≃ (G ⧸ H) × H :=
  groupEquivQuotientProdSubgroup

variable {G : Type*} [Group G]

theorem conjugate_mem (H : Subgroup G) (g : G) (h : H) : g * h * g⁻¹ ∈ conjugate g H := by
  simp [conjugate]

lemma conjugate_one (H : Subgroup G) : conjugate 1 H = H := by
  ext x
  constructor <;> intro h
  case mpr =>
    simpa [conjugate]
  case mp =>
    simpa [conjugate] using h

instance : MulAction G (Subgroup G) where
  smul g H := conjugate g H /- g • H • g⁻¹ を返す -/
  one_smul := by
    intro H
    dsimp [(· • ·)]
    apply conjugate_one
    done
  mul_smul := by
    intro x y H
    dsimp [(· • ·)]
    simp [conjugate]
    ext g
    simp only [Set.mem_setOf_eq]
    constructor <;> intro h
    · obtain ⟨h, hmem, hg⟩ := h
      use y * h * y⁻¹
      simp [mul_left_inj, mul_right_inj, exists_eq_right', hmem, hg]
      ac_rfl
    · obtain ⟨v, ⟨w, wmem, hw⟩, hmem, hg⟩ := h
      use y⁻¹ * v * y
      constructor
      · rw [hw]
        simpa [mul_assoc]
      · simp [mul_assoc]

end GroupActions

-- 商群
noncomputable section QuotientGroup

-- 正規部分群で割ると、商が群になる
example {G : Type*} [Group G] (H : Subgroup G) [H.Normal] : Group (G ⧸ H) := inferInstance

-- G から商群 G / H への自然な準同型がある
example {G : Type*} [Group G] (H : Subgroup G) [H.Normal] : G →* G ⧸ H :=
  QuotientGroup.mk' H

-- N → G - φ → M
example {G : Type*} [Group G] (N : Subgroup G) [N.Normal] {M : Type*}
    [Group M] (φ : G →* M) (h : N ≤ MonoidHom.ker φ) : G ⧸ N →* M :=
  QuotientGroup.lift N φ h

example {G : Type*} [Group G] {M : Type*} [Group M] (φ : G →* M) :
    G ⧸ MonoidHom.ker φ →* MonoidHom.range φ :=
  QuotientGroup.quotientKerEquivRange φ

example {G G': Type*} [Group G] [Group G']
    {N : Subgroup G} [N.Normal] {N' : Subgroup G'} [N'.Normal]
    {φ : G →* G'} (h : N ≤ Subgroup.comap φ N') : G ⧸ N →* G' ⧸ N':=
  QuotientGroup.map N N' φ h

example {G : Type*} [Group G] {M N : Subgroup G} [M.Normal]
    [N.Normal] (h : M = N) : G ⧸ M ≃* G ⧸ N := QuotientGroup.quotientMulEquivOfEq h

#check HEq

section
variable {G : Type*} [Group G] {H K : Subgroup G}

open MonoidHom

#check card_pos -- The nonempty argument will be automatically inferred for subgroups
#check Subgroup.index_eq_card
#check Subgroup.index_mul_card
#check Nat.eq_of_mul_eq_mul_right

-- The following line is working around a Lean bug that will be fixed very soon.
attribute [-instance] Subtype.instInhabited

-- |G| = |H| × |K| ならば |G / H| = |K|
lemma aux_card_eq [Fintype G] (h' : card G = card H * card K) : card (G ⧸ H) = card K := by
  have : card G = card H * H.index := by rw [Nat.mul_comm, @index_mul_card]
  rw [this] at h'

  have pos : card ↥H > 0 := card_pos

  rw [← Subgroup.index_eq_card]
  replace h' := Nat.eq_of_mul_eq_mul_left pos h'
  assumption

-- H と K は G の正規部分群
-- H ∩ K = {1}
-- |G| = |H| × |K|
variable [H.Normal] [K.Normal] [Fintype G] (h : Disjoint H K) (h' : card G = card H * card K)

-- 有限群に関しては、単射があって位数が等しければ同型もある
#check bijective_iff_injective_and_card

-- f が単射であることと、核が自明であることが同値
#check ker_eq_bot_iff

-- モノイド準同型をサブモノイドに制限
#check restrict

-- H ∩ K を H の部分群だと思ったもの
#check subgroupOf

-- f の制限の Ker は、f の Ker との共通部分
#check ker_restrict

open Function

/-- H ∩ K = {1} で、|G| = |H| * |K| ならば、K は G / H と同型 -/
def iso₁ [Fintype G] (h : Disjoint H K) (h' : card G = card H * card K) : K ≃* G ⧸ H := by
  -- 商群への自然な準同型
  let f : G →* G ⧸ H := QuotientGroup.mk' H

  -- f の定義域を K に制限したもの
  let φ : K →* G ⧸ H := restrict f K

  -- φ が単射であることを示す
  have inj : Injective φ := by
    -- 核が自明であることを示せばよい
    rw [← ker_eq_bot_iff φ]

    -- φ の核を、f の核で表現する
    rw [ker_restrict]

    -- f は G から G / H への自然な準同型なので、
    -- f の核は H に等しい
    have : f.ker = H := QuotientGroup.ker_mk' H
    rw [this]

    -- H と K は Disjoint という仮定があるので、
    -- H ∩ K = {1} である
    exact subgroupOf_eq_bot.mpr h

  -- φ が単射であることと、位数が等しいことから、φ は全単射である
  have bij : Bijective φ := by
    rw [bijective_iff_injective_and_card (f := φ)]

    -- φ が単射なのはさっき示した
    refine ⟨inj, ?_⟩

    -- 位数が等しいことは仮定とさっき示した aux_card_eq から
    have lem := aux_card_eq h'
    rw [lem]

  -- φ が全単射であることから、特に同型である
  exact MulEquiv.ofBijective (hf := bij)

-- H と K は G の正規部分群
-- H ∩ K = {1}
-- |G| = |H| × |K|
variable [H.Normal] [K.Normal] [Fintype G] (h : Disjoint H K) (h' : card G = card H * card K)

/-- G は G / K と G / H の直積と同型 -/
def iso₂ : G ≃* (G ⧸ K) × (G ⧸ H) := by
  -- 準同型 G → G / K
  let fk : G →* G ⧸ K := QuotientGroup.mk' K

  -- 準同型 G → G / H
  let fh : G →* G ⧸ H := QuotientGroup.mk' H

  -- 準同型 G → G / K × G / H を構成できる
  let f : G →* (G ⧸ K) × (G ⧸ H) := MonoidHom.prod fk fh

  -- f が単射であることを示す
  have inj : Injective f := by
    -- f の核が自明であることを示せばよい
    rw [← ker_eq_bot_iff f]

    -- f の核は、fk と fh の核の共通部分で書ける
    rw [ker_prod]

    -- fk の核と fh の核はそれぞれ K と H に等しい
    have k_ker : fk.ker = K := QuotientGroup.ker_mk' K
    have h_ker : fh.ker = H := QuotientGroup.ker_mk' H
    rw [k_ker, h_ker]

    -- K ∩ H は仮定から自明になる
    exact disjoint_iff.mp (_root_.id (Disjoint.symm h))

  -- f の単射性と、始域と終域の位数が等しいことから、f は全単射になる
  have bij : Bijective f := by
    rw [bijective_iff_injective_and_card (f := f)]

    -- f が単射なのはさっき示した
    refine ⟨inj, ?_⟩

    -- 直積の位数は位数の積
    rw [card_prod]

    -- 後は aux_card_eq から従う
    have lem := aux_card_eq h'
    have h'' : card G = card ↥K * card ↥H := by rw [Nat.mul_comm, h']
    have lem' := aux_card_eq h''
    rw [lem, lem']
    assumption

  -- f が全単射であることから、特に同型である
  exact MulEquiv.ofBijective (hf := bij)

-- 直積は同型を保つ。つまり、
-- M ≅* M' かつ N ≅* N' ならば M × N ≅* M' × N'
#check MulEquiv.prodCongr

def finalIso : G ≃* H × K := by
  -- iso₁ から従うことをまとめておく
  have lemH : K ≃* G ⧸ H := iso₁ h h'
  have lemK : H ≃* G ⧸ K := iso₁ (Disjoint.symm h) (by rw [Nat.mul_comm, h'])

  -- iso₂ から、G ≅* G / K × G / H が得られる
  have lem : G ≃* (G ⧸ K) × (G ⧸ H) := iso₂ h h'

  -- 後は直積が同型を保つことから示すことができる
  have := MulEquiv.prodCongr lemK lemH

  -- 同型が推移的かつ対称的であることから従う
  exact MulEquiv.trans lem this.symm
