{-# OPTIONS --safe --without-K --postfix-projections #-}

open import Algebra.Po
open import Function.Base using (flip; _∘_)
open import Level using (Level; 0ℓ)
open import Relation.Binary using (Rel; IsPreorder; Reflexive; Transitive)

module Generic.Linear.Thinning.Properties
  (Ty : Set) (poSemiring : PoSemiring 0ℓ 0ℓ 0ℓ)
  where

  open PoSemiring poSemiring
    renaming (Carrier to Ann; _≤_ to _⊴_; refl to ⊴-refl; trans to ⊴-trans)

  open import Algebra.Relational
  open import Data.Product
  open import Data.Sum
  open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
  open import Relation.Unary

  open import Data.LTree
  open import Data.LTree.Vector

  open import Generic.Linear.Operations rawPoSemiring
  open import Generic.Linear.Algebra poSemiring
  open import Generic.Linear.Syntax Ty Ann
  open import Generic.Linear.Environment Ty poSemiring
  open import Generic.Linear.Thinning Ty poSemiring
  open import Generic.Linear.Variable Ty rawPoSemiring
  -- open import Generic.Linear.Extend Ty poSemiring

  open _─Env

  private
    variable
      PΓ QΔ RΘ : Ctx
      ℓ : Level
      T : Ctx → Set ℓ
      𝓥 : Scoped ℓ
      s t u : LTree
      P P′ Q Q′ R : Vector Ann s
      A : Ty

  -- Also, Thinnable ⇒ IsPresheaf via subuse-th
  psh^LVar : IsPresheaf LVar
  idx (psh^LVar QP lv) = idx lv
  tyq (psh^LVar QP lv) = tyq lv
  basis (psh^LVar QP lv) = ⊴*-trans QP (basis lv)

  -- Possible lemma: if we have `Thinning PΓ QΔ` and `P ≤ R`, then `Q ≤ MR`.
  th^LVar : Thinnable (LVar A)
  th^LVar v th = th .lookup (th .sums) v

  {-
  -- The rows of a thinning's matrix are a selection of standard basis vectors
  -- (i.e, rows from the identity matrix).
  -- Which rows, exactly, is defined by the action of the thinning (lookup).
  thinning-sub-1ᴹ :
    ∀ {PΓ QΔ A}
    (th : Thinning PΓ QΔ) (v : Var A (Ctx.Γ PΓ)) →
    M th (v .idx) ⊴* 1ᴹ (th .lookup v .idx)
  thinning-sub-1ᴹ {ctx {[-]} P Γ} {ctx {t} Q Δ} th v@(var here q) =
    th .lookup v .basis
  thinning-sub-1ᴹ {PΓ} th (var (↙ i) q) =
    thinning-sub-1ᴹ
      {leftᶜ (ctx→sctx PΓ)}
      record { M = topᴹ (th .M); sums = ⊴*-refl; lookup = th .lookup ∘ leftᵛ }
      (var i q)
  thinning-sub-1ᴹ {PΓ} th (var (↘ i) q) =
    thinning-sub-1ᴹ
      {rightᶜ (ctx→sctx PΓ)}
      record { M = botᴹ (th .M); sums = ⊴*-refl; lookup = th .lookup ∘ rightᵛ }
      (var i q)
  -}

  identity : Thinning PΓ PΓ
  identity .M = idLinMor
  identity .asLinRel = idAsLinRel
  identity .sums = ⊴*-refl
  identity .lookup le v = record { LVar v; basis = ⊴*-trans le (v .basis) }

  select : ∀ {PΓ QΔ RΘ : Ctx} → let ctx R Θ = RΘ in
           Thinning PΓ QΔ → (QΔ ─Env) 𝓥 RΘ → (PΓ ─Env) 𝓥 RΘ
  select th ρ .M = th .M >>LinMor ρ .M
  select th ρ .asLinRel = th .asLinRel >>AsLinRel ρ .asLinRel
  select th ρ .sums = th .sums , ρ .sums
  select th ρ .lookup (th-r , ρ-r) v = ρ .lookup ρ-r (th .lookup th-r v)

  {-
  instance
    re^LVar : RightExtend LVar
    re^LVar .embedVarʳ (var i q) = lvar (↙ i) q (⊴*-refl ++₂ ⊴*-refl)

    le^LVar : LeftExtend LVar
    le^LVar .embedVarˡ (var i q) = lvar (↘ i) q (⊴*-refl ++₂ ⊴*-refl)
  -}

  subuse-th : ∀ {Γ} → Q ⊴* P → Thinning (ctx P Γ) (ctx Q Γ)
  subuse-th QP .M = idLinMor
  subuse-th QP .asLinRel = idAsLinRel
  subuse-th QP .sums = QP
  subuse-th QP .lookup QP′ v = psh^LVar QP′ v

  extract : ∀[ □ T ⇒ T ]
  extract t = t identity

  duplicate : ∀[ □ T ⇒ □ (□ T) ]
  duplicate t ρ σ = t (select ρ σ)

  th^□ : Thinnable (□ T)
  th^□ = duplicate
