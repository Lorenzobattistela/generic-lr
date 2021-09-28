{-# OPTIONS --sized-types --without-K --prop --postfix-projections #-}

open import Algebra.Po
open import Level using (Level; 0ℓ; suc)
open import Relation.Binary using (Rel)

module Generic.Linear.Example.UsageCheck (Ty : Set) where

  open import Data.Empty
  open import Data.List as L using (List; []; _∷_)
  open import Data.Unit hiding (_≤_)
  open import Proposition

  Lone : ∀ {a} {A : Set a} → List A → Set
  Lone [] = ⊥
  Lone (x ∷ []) = ⊤
  Lone (x ∷ y ∷ _) = ⊥

  getLone : ∀ {a} {A : Set a} (xs : List A) {_ : Lone xs} → A
  getLone (x ∷ []) = x

  module U where

    0-poSemiring : PoSemiring 0ℓ 0ℓ 0ℓ
    0-poSemiring = record { Carrier = ⊤; _≈_ = λ _ _ → ⊤; _≤_ = λ _ _ → ⊤ }

    0-rawPoSemiring : RawPoSemiring 0ℓ 0ℓ 0ℓ
    0-rawPoSemiring = PoSemiring.rawPoSemiring 0-poSemiring

    open import Generic.Linear.Everything Ty 0-poSemiring public

  module WithPoSemiring (poSemiring : PoSemiring 0ℓ 0ℓ 0ℓ) where

    open import Generic.Linear.Everything Ty poSemiring hiding (pure)

    private
      variable
        fl : PremisesFlags

    uCtx : Ctx → U.Ctx
    uCtx (ctx P γ) = U.ctx _ γ

    uPremises : Premises fl → U.Premises fl
    uPremises ⟨ Γ `⊢ A ⟩ = U.⟨ uCtx Γ `⊢ A ⟩
    uPremises `⊤ = U.`⊤
    uPremises `ℑ = U.`ℑ
    uPremises (ps `∧ qs) = uPremises ps U.`∧ uPremises qs
    uPremises (ps `✴ qs) = uPremises ps U.`✴ uPremises qs
    uPremises (r `· ps) = _ U.`· uPremises ps
    uPremises (`□ bf ps) = U.`□ bf (uPremises ps)
    uRule : Rule fl → U.Rule fl
    uRule (ps =⇒ A) = uPremises ps U.=⇒ A
    uSystem : System fl → U.System fl
    uSystem (L ▹ rs) = L U.▹ λ l → uRule (rs l)

    open import Category.Functor
    open import Category.Monad
    open import Data.Bool.Extra
    open import Data.List.Categorical
    open RawFunctor (functor {0ℓ}) using (_<$>_)
    open RawMonad (monad {0ℓ}) using (pure; _>>=_) renaming (_⊛_ to _<*>_)
    open import Data.LTree
    open import Data.LTree.Vector as V hiding ([]; [_]; _++_)
    open import Data.Product as × hiding (_<*>_)
    open import Data.Product.Relation.Binary.Pointwise.NonDependent as ×
    open import Data.Wrap
    open import Function.Base using (_∘_; _$_)
    open import Relation.Nary
    open import Relation.Unary.Bunched
    open BunchedDuplicable
    open import Size

    record NonDetInverses (fl : PremisesFlags) : Set where
      open PremisesFlags fl
      field
        0#⁻¹ : (r : Ann) → List (r ≤ 0#)
        +⁻¹ : (r : Ann) → List (∃ \ ((p , q) : Ann × Ann) → r ≤ p + q)
        1#⁻¹ : (r : Ann) → List (r ≤ 1#)
        *⁻¹ : (r q : Ann) → List (∃ \ p → q ≤ r * p)
        rep : {{_ : Has-□}} (bf : BoxFlags) (r : Ann) →
          List (Dup _≤_ _≤0 _≤[_+_] _≤[_*_] bf (λ _ → ⊤) r)
              -- List (∃ \ p → r ≤ p × p ≤ 0# × p ≤ p + p)

    module WithInverses (fl : PremisesFlags) (invs : NonDetInverses fl) where

      open PremisesFlags fl
      open NonDetInverses invs

      0*⁻¹ : ∀ {s} (R : Vector Ann s) → List (R ≤0*)
      0*⁻¹ {[-]} R = (| [_]ₙ (0#⁻¹ (R here)) |)
      0*⁻¹ {ε} R = (| []ₙ |)
      0*⁻¹ {s <+> t} R = (| _++ₙ_ (0*⁻¹ (R ∘ ↙)) (0*⁻¹ (R ∘ ↘)) |)

      +*⁻¹ : ∀ {s} (R : Vector Ann s) →
             List (∃ \ ((P , Q) : _ × _) → R ≤[ P +* Q ])
      +*⁻¹ {[-]} R = (| (×.map (×.map V.[_] V.[_]) [_]ₙ) (+⁻¹ (R here)) |)
      +*⁻¹ {ε} R = (| ((V.[] , V.[]) , []ₙ) |)
      +*⁻¹ {s <+> t} R =
        (| (×.zip (×.zip V._++_ V._++_) _++ₙ_) (+*⁻¹ (R ∘ ↙)) (+*⁻¹ (R ∘ ↘)) |)

      ⟨_∣⁻¹ : ∀ {s} (i : Ptr s) R → List (R ≤* ⟨ i ∣)
      ⟨ here ∣⁻¹ R = (| [_]ₙ (1#⁻¹ (R here)) |)
      ⟨ ↙ i ∣⁻¹ R = (| _++ₙ_ (⟨ i ∣⁻¹ (R ∘ ↙)) (L.map 0*→≤* (0*⁻¹ (R ∘ ↘))) |)
      ⟨ ↘ i ∣⁻¹ R = (| _++ₙ_ (L.map 0*→≤* (0*⁻¹ (R ∘ ↙))) (⟨ i ∣⁻¹ (R ∘ ↘)) |)

      *ₗ⁻¹ : ∀ {s} r (Q : Vector Ann s) → List (∃ \ P → Q ≤[ r *ₗ P ])
      *ₗ⁻¹ {[-]} r Q = (| (×.map V.[_] [_]ₙ) (*⁻¹ r (Q here)) |)
      *ₗ⁻¹ {ε} r Q = (| (V.[] , []ₙ) |)
      *ₗ⁻¹ {s <+> t} r Q =
        (| (×.zip V._++_ _++ₙ_) (*ₗ⁻¹ r (Q ∘ ↙)) (*ₗ⁻¹ r (Q ∘ ↘)) |)

      rep* : ∀ {{_ : Has-□}} (bf : BoxFlags) {s} (R : Vector Ann s) →
        List (Dup _≤*_ _≤0* _≤[_+*_] _≤[_*ₗ_] bf (λ _ → ⊤) R)
      rep* bf {[-]} R = do
        □⟨ str , sp0 , sp+ , sp* ⟩ _ ← rep bf (R here)
        pure $ □⟨_,_,_,_⟩_ {y = V.[ _ ]} [ str ]ₙ (map-If [_]ₙ sp0)
          (map-If [_]ₙ sp+) (map-If (λ z r → [ z r ]ₙ) sp*) _
      rep* bf {ε} R = pure $
        □⟨_,_,_,_⟩_ {y = V.[]} []ₙ (pure-If []ₙ) (pure-If []ₙ)
          (pure-If (λ r → []ₙ)) _
      rep* bf {s <+> t} R = do
        □⟨ strl , sp0l , sp+l , sp*l ⟩ _ ← rep* bf {s} (R ∘ ↙)
        □⟨ strr , sp0r , sp+r , sp*r ⟩ _ ← rep* bf {t} (R ∘ ↘)
        pure $ □⟨_,_,_,_⟩_ {y = _ V.++ _} (strl ++ₙ strr)
          (zip-If _++ₙ_ sp0l sp0r) (zip-If _++ₙ_ sp+l sp+r)
          (zip-If (λ x y r → x r ++ₙ y r) sp*l sp*r) _

      lemma-p :
        ∀ (sys : System fl) (ps : Premises fl) {Γ} →
        U.⟦ uPremises ps ⟧p
          (U.Scope λ (U.ctx _ δ) B → ∀ Q → List ([ sys , ∞ ] ctx Q δ ⊢ B))
          (uCtx Γ) →
        List (⟦ ps ⟧p (Scope [ sys , ∞ ]_⊢_) Γ)
      lemma-p sys ⟨ ctx Q δ `⊢ A ⟩ {ctx P γ} t = t (P V.++ Q)
      lemma-p sys `⊤ t = (| t |)
      lemma-p sys `ℑ t = (| ℑ⟨_⟩ (0*⁻¹ _) |)
      lemma-p sys (ps `∧ qs) (s , t) =
        (| _,_ (lemma-p sys ps s) (lemma-p sys qs t) |)
      lemma-p sys (ps `✴ qs) {ctx P γ} (s ✴⟨ _ ⟩ t) = do
        ((Pl , Pr) , sp) ← +*⁻¹ P
        (| _✴⟨ sp ⟩_ (lemma-p sys ps s) (lemma-p sys qs t) |)
      lemma-p sys (r `· ps) {ctx P γ} (⟨ _ ⟩· t) = do
        (P′ , sp) ← *ₗ⁻¹ r P
        (| ⟨ sp ⟩·_ (lemma-p sys ps t) |)
      lemma-p sys (`□ bf ps) {ctx P γ} (□⟨ _ , _ , _ , _ ⟩ t) = do
        (□⟨ str , sp0 , sp+ , sp* ⟩ _) ← rep* bf P
        (| □⟨ str , sp0 , sp+ , sp* ⟩_ (lemma-p sys ps t) |)

      lemma-r :
        ∀ (sys : System fl) (r : Rule fl) {A Γ} →
        U.⟦ uRule r ⟧r
          (U.Scope λ (U.ctx _ δ) B → ∀ Q → List ([ sys , ∞ ] ctx Q δ ⊢ B))
          (uCtx Γ) A →
        List (⟦ r ⟧r (Scope [ sys , ∞ ]_⊢_) Γ A)
      lemma-r sys (ps =⇒ B) (q , t) = (| (q ,_) (lemma-p sys ps t) |)

      lemma :
        ∀ (sys : System fl) {A Γ} →
        U.⟦ uSystem sys ⟧s
          (U.Scope λ (U.ctx _ δ) B → ∀ Q → List ([ sys , ∞ ] ctx Q δ ⊢ B))
          (uCtx Γ) A →
        List (⟦ sys ⟧s (Scope [ sys , ∞ ]_⊢_) Γ A)
      lemma sys@(L ▹ rs) (l , t) = (| (l ,_) (lemma-r sys (rs l) t) |)

      module _ (sys : System fl) where

        𝓒 : U.OpenFam _
        𝓒 (U.ctx _ γ) A = ∀ R → List ([ sys , ∞ ] ctx R γ ⊢ A)

        open Semantics using (ren^𝓥; ⟦var⟧; ⟦con⟧)

        elab-sem : U.Semantics (uSystem sys) U._∋_ 𝓒
        elab-sem .ren^𝓥 (U.lvar i q _) ρ =
          let v = ρ .U.lookup (ρ .sums) (U.lvar i q _) in
          U.lvar (v .U.idx) (v .U.tyq) _
          where open [_]_⇒ᵉ_
        elab-sem .⟦var⟧ (U.lvar i q _) R =
          (| `var (| (lvar i q) (⟨ i ∣⁻¹ R) |) |)
        elab-sem .⟦con⟧ b R =
          let foo = U.map-s′ (uSystem sys) U.reify b in
          (| `con (lemma sys foo) |)

        elab : ∀ {A s} {γ : Vector Ty s} →
               U.[ uSystem sys , ∞ ] U.ctx _ γ ⊢ A →
               ∀ R → List ([ sys , ∞ ] ctx R γ ⊢ A)
        elab = semantics U.identity
          where open U.Semantics elab-sem

        elab-unique :
          ∀ {A s} {γ : Vector Ty s} →
          (M : U.[ uSystem sys , ∞ ] U.ctx _ γ ⊢ A) →
          ∀ R → {_ : Lone (elab M R)} → [ sys , ∞ ] ctx R γ ⊢ A
        elab-unique M R {l} with uM ∷ [] ← elab M R = uM
