{-# OPTIONS --safe --without-K --postfix-projections #-}

open import Algebra using (Op₂)
open import Level using (0ℓ)
open import Relation.Binary using (Rel)

module Specific.Syntax
  (Ann : Set) (_⊴_ : Rel Ann 0ℓ)
  (0# : Ann) (_+_ : Op₂ Ann) (1# : Ann) (_*_ : Op₂ Ann)
  where

  open import Data.LTree
  open import Data.LTree.Vector
  open import Data.LTree.Matrix
  open import Relation.Binary.PropositionalEquality

-- 0 is the unit type for sum types A ⊕ B
-- 1 is the unit type for tensor prod types A ⊗ B  
  open Ident 0# 1#

  private
    variable
      π ρ : Ann -- annotation
      t : LTree

-- bin relation of skew semirings ⊴
  infix 4 _⊴*_ _⊴ᴹ_
  infixr 6 _+*_
  infixr 7 _*ₗ_

  _⊴*_ = Lift₂ _⊴_
  _⊴ᴹ_ = Lift₂ᴹ _⊴_
  0* = lift₀ 0#
  _+*_ = lift₂ _+_
  _*ₗ_ : Ann → Vector Ann t → Vector Ann t
  ρ *ₗ R = lift₁ (ρ *_) R

  infixr 5 _t⊸_
  infixr 6 _t&_ _t⊕_
  infixr 7 _t⊗_

  data Ty : Set where
    -- types: tl is the base type
    tι : Ty
    -- unit types
    tI t⊤ t0 : Ty
    _t⊸_ _t⊗_ _t⊕_ _t&_ : (A B : Ty) → Ty
    t! : (ρ : Ann) (A : Ty) → Ty

  private
    variable
      A B C : Ty

  open import Generic.Linear.Syntax Ty Ann
  open Ctx public renaming (s to shape; R to use-ctx; Γ to ty-ctx)
-- indexed var w type equality proof
  record IVar {s} (Γ : Vector Ty s) (A : Ty) : Set where
    constructor ivar
    field
      idx : Ptr s
      ty-eq : Γ idx ≡ A

-- linear variable -> type equality and basis condition
  record LVar (PΓ : Ctx) (A : Ty) : Set where
    constructor lvar
    private
      s = PΓ .shape ; P = PΓ .use-ctx ; Γ = PΓ .ty-ctx
    field
      idx : Ptr s
      ty-eq : Γ idx ≡ A
      basis : P ⊴* 1ᴹ idx

    iVar : IVar Γ A
    iVar .IVar.idx = idx
    iVar .IVar.ty-eq = ty-eq

  pattern ivar! i = ivar i refl
  pattern lvar! i sp = lvar i refl sp

  open IVar public
  open LVar public

-- equips an IVar with a basis condition to create LVar
  equip-var : ∀ {s Γ R} (i : IVar Γ A) → R ⊴* 1ᴹ (i .idx) →
              LVar (ctx {s} R Γ) A
  equip-var i sp .idx = i .idx
  equip-var i sp .ty-eq = i .ty-eq
  equip-var i sp .basis = sp

  private
    variable
      P Q R : Vector Ann _

-- terms in labda calculus
  data Tm (RΓ : Ctx) : Ty → Set where
    -- var: a linear variable with context R and gamma
    var : LVar RΓ A → Tm RΓ A -- creates a var term w ctx RΓ of type A
    -- lvar contains the index (de brujin) type eq proof and basis condition

    -- application term with splitting condition
    -- takes two subterms M and M where M is a term of type A t⊸ B (a linear function type) in context ctx P Γ and N is a term of type A in context ctx Q Γ
    -- the sp argument is a splitting condition that ensures R ⊴* P +* Q meaning the context R can be split into P and Q
    app : let ctx R Γ = RΓ in
          (M : Tm (ctx P Γ) (A t⊸ B)) (N : Tm (ctx Q Γ) A)
          (sp : R ⊴* P +* Q) → Tm RΓ B
    
    -- lambda abstraction term
    -- takes a subterm M of type B in the extended context RΓ ++ᶜ [ 1# · A ]ᶜ where A is the type of the bound variable
    lam : (M : Tm (RΓ ++ᶜ [ 1# · A ]ᶜ) B) → Tm RΓ (A t⊸ B)

    -- unit elimination with splitting condition
    unm : let ctx R Γ = RΓ in
          (M : Tm (ctx P Γ) tI) (N : Tm (ctx Q Γ) C) (sp : R ⊴* P +* Q) →
          Tm RΓ C
      
    -- unit introduction term with splitting condition
    uni : let ctx R Γ = RΓ in (sp : R ⊴* 0*) → Tm RΓ tI

    -- tensor product elimination w split
    prm : let ctx R Γ = RΓ in
          (M : Tm (ctx P Γ) (A t⊗ B))
          (N : Tm (ctx Q Γ ++ᶜ ([ 1# · A ]ᶜ ++ᶜ [ 1# · B ]ᶜ)) C)
          (sp : R ⊴* P +* Q) → Tm RΓ C

    -- tensor product introduction elimination w splitting condition
    ten : let ctx R Γ = RΓ in
          (M : Tm (ctx P Γ) A) (N : Tm (ctx Q Γ) B) (sp : R ⊴* P +* Q) →
          Tm RΓ (A t⊗ B)

    -- ex falso term w splitting condition
    exf : let ctx R Γ = RΓ in
          (M : Tm (ctx P Γ) t0) (sp : R ⊴* P +* Q) → Tm RΓ C
    -- no t0 introduction
    cse : let ctx R Γ = RΓ in
          (M : Tm (ctx P Γ) (A t⊕ B))
          (N : Tm (ctx Q Γ ++ᶜ [ 1# · A ]ᶜ) C)
          (O : Tm (ctx Q Γ ++ᶜ [ 1# · B ]ᶜ) C)
          (sp : R ⊴* P +* Q) → Tm RΓ C
      
    -- left and right injection terms for sum types
    inl : (M : Tm RΓ A) → Tm RΓ (A t⊕ B)
    inr : (M : Tm RΓ B) → Tm RΓ (A t⊕ B)

    -- no t⊤ elimination
    top : Tm RΓ t⊤
    prl : (M : Tm RΓ (A t& B)) → Tm RΓ A
    prr : (M : Tm RΓ (A t& B)) → Tm RΓ B
    wth : (M : Tm RΓ A) (N : Tm RΓ B) → Tm RΓ (A t& B)

    bam : let ctx R Γ = RΓ in
          (M : Tm (ctx P Γ) (t! ρ A)) (N : Tm (ctx Q Γ ++ᶜ ([ ρ · A ]ᶜ)) C)
          (sp : R ⊴* P +* Q) → Tm RΓ C
    bng : let ctx R Γ = RΓ in
          (M : Tm (ctx P Γ) A) (sp : R ⊴* ρ *ₗ P) → Tm RΓ (t! ρ A)

The syntax definitions in the linear lambda calculus ensure linearity by incorporating usage annotations and splitting conditions. Let's explore how linearity is enforced and how renaming, substitution, subuse, and traversal apply to the syntax.

1. Linearity:
   - In the linear lambda calculus, each variable must be used exactly once. This is enforced through the usage annotations (`Ann`) and the splitting conditions (`_⊴*_`, `_+*_`, `_*ₗ_`).
   - The usage annotations keep track of how many times a variable is used. For example, `0#` represents zero uses, `1#` represents one use, and `_+_` combines the usage annotations.
   - The splitting conditions ensure that the usage annotations are properly divided among subterms. For example, in the `app` constructor, the condition `sp : R ⊴* P +* Q` ensures that the usage annotation `R` can be split into `P` and `Q`, which are used by the subterms `M` and `N`, respectively.
   - The `LVar` record, used in the `var` constructor, includes a `basis` field that ensures the variable has a usage annotation of `1#` in the context, enforcing linear usage.

2. Renaming:
   - Renaming variables is an important operation in lambda calculi to avoid name clashes during substitution.
   - In the linear lambda calculus, renaming must preserve the linearity constraints. When renaming a variable, the usage annotations and splitting conditions must be updated accordingly.
   - The `IVar` and `LVar` records, which represent variables, include an `idx` field that can be used to perform renaming. By updating the `idx` field consistently across the term, variables can be renamed while maintaining linearity.

3. Substitution:
   - Substitution is the process of replacing variables with terms in a lambda calculus.
   - In the linear lambda calculus, substitution must respect the linearity constraints. When substituting a term for a variable, the usage annotations and splitting conditions must be adjusted to ensure that the substituted term is used linearly.
   - The splitting conditions in the term constructors, such as `app`, `prm`, `ten`, etc., facilitate linear substitution by distributing the usage annotations correctly among the subterms.

4. Subuse:
   - Subuse refers to the property that if a term is well-typed under a certain usage annotation, it remains well-typed under any smaller usage annotation.
   - The subuse relation `_⊴*_` captures this property. It allows a term to be used in a context with a smaller usage annotation than what it was originally typed with.
   - Subuse is important for compositionality and reuse of terms in different contexts. It enables a term to be used in a context that requires fewer resources than what the term provides.

5. Traversal:
   - Traversal refers to the process of recursively processing the structure of a term, visiting each subterm and performing some operation or analysis.
   - In the linear lambda calculus, traversal can be used to check and enforce linearity constraints, perform renaming, substitution, or other transformations on the terms.
   - The recursive nature of the term constructors, such as `app`, `lam`, `prm`, `ten`, etc., allows for traversing the term structure and applying operations to the subterms while maintaining linearity.
   - Traversal can be implemented using pattern matching on the term constructors and recursively processing the subterms, updating the usage annotations and splitting conditions as needed.

By incorporating usage annotations, splitting conditions, and carefully designing the term constructors, the linear lambda calculus syntax ensures that linearity is enforced. Renaming, substitution, subuse, and traversal can be performed on the terms while respecting the linearity constraints, enabling safe and correct manipulation of linear terms.

The syntax definitions provide a foundation for building a type system and operational semantics for the linear lambda calculus, ensuring that the desired properties of linearity are maintained throughout the evaluation and transformation of terms.