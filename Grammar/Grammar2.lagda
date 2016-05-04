\begin{code}
module Grammar.Grammar2 where

open import Function
open import Data.List
open import Prelims
open import Grammar

record ToGrammar' (T : Taxonomy) : Set₁ where
  open Taxonomy T
  field
    Constructor    : ∀ {K} → Kind' (-Constructor K) → Set
    parent         : VarKind → ExpressionKind

  data Subexpression : Alphabet → ∀ C → Kind' C → Set
  Expression : Alphabet → ExpressionKind → Set
  Body : Alphabet → ∀ {K} → Kind' (-Constructor K) → Set

  Expression V K = Subexpression V -Expression (base K)
  Body V {K} C = Subexpression V (-Constructor K) C

  infixr 50 _,,_
  data Subexpression where
    var : ∀ {V} {K} → Var V K → Expression V (varKind K)
    app : ∀ {V} {K} {C} → Constructor C → Body V {K} C → Expression V K
    out : ∀ {V} {K} → Body V {K} out
    _,,_ : ∀ {V} {K} {A} {L} {C} → Expression (extend' V A) L → Body V {K} C → Body V (Π A L C)

  var-inj : ∀ {V} {K} {x y : Var V K} → var x ≡ var y → x ≡ y
  var-inj refl = refl

  record PreOpFamily : Set₂ where
      field
        Op : Alphabet → Alphabet → Set
        apV : ∀ {U} {V} {K} → Op U V → Var U K → Expression V (varKind K)
        up : ∀ {V} {K} → Op V (V , K)
        apV-up : ∀ {V} {K} {L} {x : Var V K} → apV (up {K = L}) x ≡ var (↑ x)
        idOp : ∀ V → Op V V
        apV-idOp : ∀ {V} {K} (x : Var V K) → apV (idOp V) x ≡ var x

      _∼op_ : ∀ {U} {V} → Op U V → Op U V → Set
      _∼op_ {U} {V} ρ σ = ∀ {K} (x : Var U K) → apV ρ x ≡ apV σ x
    
      ∼-refl : ∀ {U} {V} {σ : Op U V} → σ ∼op σ
      ∼-refl _ = refl
    
      ∼-sym : ∀ {U} {V} {σ τ : Op U V} → σ ∼op τ → τ ∼op σ
      ∼-sym σ-is-τ x = sym (σ-is-τ x)

      ∼-trans : ∀ {U} {V} {ρ σ τ : Op U V} → ρ ∼op σ → σ ∼op τ → ρ ∼op τ
      ∼-trans ρ-is-σ σ-is-τ x = trans (ρ-is-σ x) (σ-is-τ x)

      OP : Alphabet → Alphabet →  Setoid _ _
      OP U V = record { 
        Carrier = Op U V ; 
        _≈_ = _∼op_ ; 
        isEquivalence = record { 
          refl = ∼-refl ; 
          sym = ∼-sym ; 
          trans = ∼-trans } }

      record Lifting : Set₁ where
        field
          liftOp : ∀ {U} {V} K → Op U V → Op (U , K) (V , K)
          liftOp-cong : ∀ {V} {W} {K} {ρ σ : Op V W} → ρ ∼op σ → liftOp K ρ ∼op liftOp K σ
\end{code}

Given an operation $\sigma : U \rightarrow V$ and an abstraction kind $(x_1 : A_1 , \ldots , x_n : A_n) B$, define
the \emph{repeated lifting} $\sigma^A$ to be $((\cdots(\sigma , A_1) , A_2) , \cdots ) , A_n)$.

\begin{code}
        liftOp' : ∀ {U} {V} A → Op U V → Op (extend' U A) (extend' V A)
        liftOp' [] σ = σ
        liftOp' (K ∷ A) σ = liftOp' A (liftOp K σ)
--TODO Refactor to deal with sequences of kinds instead of abstraction kinds?

        liftOp'-cong : ∀ {U} {V} A {ρ σ : Op U V} → ρ ∼op σ → liftOp' A ρ ∼op liftOp' A σ
        liftOp'-cong [] ρ-is-σ = ρ-is-σ
        liftOp'-cong (_ ∷ A) ρ-is-σ = liftOp'-cong A (liftOp-cong ρ-is-σ)

        ap : ∀ {U} {V} {C} {K} → Op U V → Subexpression U C K → Subexpression V C K
        ap ρ (var x) = apV ρ x
        ap ρ (app c EE) = app c (ap ρ EE)
        ap _ out = out
        ap ρ (_,,_ {A = A} {L = L} E EE) = _,,_ (ap (liftOp' A ρ) E) (ap ρ EE)

        ap-congl : ∀ {U} {V} {C} {K} {ρ σ : Op U V} (E : Subexpression U C K) →
          ρ ∼op σ → ap ρ E ≡ ap σ E
        ap-congl (var x) ρ-is-σ = ρ-is-σ x
        ap-congl (app c E) ρ-is-σ = cong (app c) (ap-congl E ρ-is-σ)
        ap-congl out _ = refl
        ap-congl (_,,_ {A = A} E F) ρ-is-σ = cong₂ _,,_ (ap-congl E (liftOp'-cong A ρ-is-σ)) (ap-congl F ρ-is-σ)

        ap-cong : ∀ {U} {V} {C} {K} {ρ σ : Op U V} {M N : Subexpression U C K} →
          ρ ∼op σ → M ≡ N → ap ρ M ≡ ap σ N
        ap-cong {ρ = ρ} {σ} {M} {N} ρ∼σ M≡N = let open ≡-Reasoning in 
          begin
            ap ρ M
          ≡⟨ ap-congl M ρ∼σ ⟩
            ap σ M
          ≡⟨ cong (ap σ) M≡N ⟩
            ap σ N
          ∎

        record IsLiftFamily : Set₁ where
          field
            liftOp-x₀ : ∀ {U} {V} {K} {σ : Op U V} → apV (liftOp K σ) x₀ ≡ var x₀
            liftOp-↑ : ∀ {U} {V} {K} {L} {σ : Op U V} (x : Var U L) →
              apV (liftOp K σ) (↑ x) ≡ ap up (apV σ x)

          liftOp-idOp : ∀ {V} {K} → liftOp K (idOp V) ∼op idOp (V , K)
          liftOp-idOp {V} {K} x₀ = let open ≡-Reasoning in
            begin
              apV (liftOp K (idOp V)) x₀
            ≡⟨ liftOp-x₀ ⟩
              var x₀
            ≡⟨⟨ apV-idOp x₀ ⟩⟩
              apV (idOp (V , K)) x₀
            ∎
          liftOp-idOp {V} {K} {L} (↑ x) = let open ≡-Reasoning in 
            begin 
              apV (liftOp K (idOp V)) (↑ x)
            ≡⟨ liftOp-↑ x ⟩
              ap up (apV (idOp V) x)
            ≡⟨ cong (ap up) (apV-idOp x) ⟩
              ap up (var x)              
            ≡⟨ apV-up ⟩
              var (↑ x)
            ≡⟨⟨ apV-idOp (↑ x) ⟩⟩
              (apV (idOp (V , K)) (↑ x)
            ∎)
       
          liftOp'-idOp : ∀ {V} A → liftOp' A (idOp V) ∼op idOp (extend' V A)
          liftOp'-idOp [] = ∼-refl
          liftOp'-idOp {V} (K ∷ A) = let open EqReasoning (OP (extend' (V , K) A) (extend' (V , K) A)) in 
            begin
              liftOp' A (liftOp K (idOp V))
            ≈⟨ liftOp'-cong A liftOp-idOp ⟩
              liftOp' A (idOp (V , K))
            ≈⟨ liftOp'-idOp A ⟩
              idOp (extend' (V , K) A)
            ∎

          ap-idOp : ∀ {V} {C} {K} {E : Subexpression V C K} → ap (idOp V) E ≡ E
          ap-idOp {E = var x} = apV-idOp x
          ap-idOp {E = app c EE} = cong (app c) ap-idOp
          ap-idOp {E = out} = refl
          ap-idOp {E = _,,_ {A = A} E F} = cong₂ _,,_ (trans (ap-congl E (liftOp'-idOp A)) ap-idOp) ap-idOp
          
  record LiftFamily : Set₂ where
      field
        preOpFamily : PreOpFamily
        lifting : PreOpFamily.Lifting preOpFamily
        isLiftFamily : PreOpFamily.Lifting.IsLiftFamily lifting
      open PreOpFamily preOpFamily public
      open Lifting lifting public
      open IsLiftFamily isLiftFamily public
\end{code}

Let $F$, $G$ and $H$ be three families of operations.  For all $U$, $V$, $W$, let $\circ$ be a function
\[ \circ : F V W \times G U V \rightarrow H U W \]

\begin{lemma}
If $\circ$ respects lifting, then it respects repeated lifting.
\end{lemma}

\begin{code}
  module Composition {F G H}
      (circ : ∀ {U} {V} {W} → LiftFamily.Op F V W → LiftFamily.Op G U V → LiftFamily.Op H U W)
      (liftOp-circ : ∀ {U V W K σ ρ} → LiftFamily._∼op_ H (LiftFamily.liftOp H K (circ {U} {V} {W} σ ρ)) (circ (LiftFamily.liftOp F K σ) (LiftFamily.liftOp G K ρ)))
      (apV-circ : ∀ {U} {V} {W} {K} {σ} {ρ} {x : Var U K} → LiftFamily.apV H (circ {U} {V} {W} σ ρ) x ≡ LiftFamily.ap F σ (LiftFamily.apV G ρ x)) where

      open LiftFamily
      
      liftOp'-circ : ∀ {U V W} A {σ ρ} → _∼op_ H (liftOp' H A (circ {U} {V} {W} σ ρ)) (circ (liftOp' F A σ) (liftOp' G A ρ))
      liftOp'-circ [] = ∼-refl H
      liftOp'-circ {U} {V} {W} (K ∷ A) {σ} {ρ} = let open EqReasoning (OP H _ _) in 
        begin
          liftOp' H A (liftOp H K (circ σ ρ))
        ≈⟨ liftOp'-cong H A liftOp-circ ⟩
          liftOp' H A (circ (liftOp F K σ) (liftOp G K ρ))
        ≈⟨ liftOp'-circ A ⟩
          circ (liftOp' F A (liftOp F K σ)) (liftOp' G A (liftOp G K ρ))
        ∎

      ap-circ : ∀ {U V W C K} (E : Subexpression U C K) {σ ρ} → ap H (circ {U} {V} {W} σ ρ) E ≡ ap F σ (ap G ρ E)
      ap-circ (var _) = apV-circ
      ap-circ (app c E) = cong (app c) (ap-circ E)
      ap-circ out = refl
      ap-circ (_,,_ {A = A} E E') {σ} {ρ} = cong₂ _,,_
        (let open ≡-Reasoning in 
        begin
          ap H (liftOp' H A (circ σ ρ)) E
        ≡⟨ ap-congl H E (liftOp'-circ A) ⟩
          ap H (circ (liftOp' F A σ) (liftOp' G A ρ)) E
        ≡⟨ ap-circ E ⟩
          ap F (liftOp' F A σ) (ap G (liftOp' G A ρ) E)
        ∎) 
        (ap-circ E')

      circ-cong : ∀ {U V W} {σ σ' : Op F V W} {ρ ρ' : Op G U V} → _∼op_ F σ σ' → _∼op_ G ρ ρ' → _∼op_ H (circ σ ρ) (circ σ' ρ')
      circ-cong {U} {V} {W} {σ} {σ'} {ρ} {ρ'} σ∼σ' ρ∼ρ' x = let open ≡-Reasoning in 
        begin
          apV H (circ σ ρ) x
        ≡⟨ apV-circ ⟩
          ap F σ (apV G ρ x)
        ≡⟨ ap-cong F σ∼σ' (ρ∼ρ' x) ⟩
          ap F σ' (apV G ρ' x)
        ≡⟨⟨ apV-circ ⟩⟩
          apV H (circ σ' ρ') x
        ∎

  record IsOpFamily (F : LiftFamily) : Set₂ where
      open LiftFamily F public
      field
          comp : ∀ {U} {V} {W} → Op V W → Op U V → Op U W
          apV-comp : ∀ {U} {V} {W} {K} {σ : Op V W} {ρ : Op U V} {x : Var U K} →
            apV (comp σ ρ) x ≡ ap σ (apV ρ x)
          liftOp-comp : ∀ {U} {V} {W} {K} {σ : Op V W} {ρ : Op U V} →
            liftOp K (comp σ ρ) ∼op comp (liftOp K σ) (liftOp K ρ)
\end{code}

The following results about operationsare easy to prove.
\begin{lemma}
  \begin{enumerate}
  \item $(\sigma , K) \circ \uparrow \sim \uparrow \circ \sigma$
  \item $(\id{V} , K) \sim \id{V,K}$
  \item $\id{V}[E] \equiv E$
  \item $(\sigma \circ \rho)[E] \equiv \sigma[\rho[E]]$
  \end{enumerate}
\end{lemma}

\begin{code}
      liftOp-up : ∀ {U} {V} {K} {σ : Op U V} → comp (liftOp K σ) up ∼op comp up σ
      liftOp-up {U} {V} {K} {σ} {L} x = 
          let open ≡-Reasoning {A = Expression (V , K) (varKind L)} in 
            begin
              apV (comp (liftOp K σ) up) x
            ≡⟨ apV-comp ⟩
              ap (liftOp K σ) (apV up x)
            ≡⟨ cong (ap (liftOp K σ)) apV-up ⟩
              apV (liftOp K σ) (↑ x)         
            ≡⟨ liftOp-↑ x ⟩
              ap up (apV σ x)
            ≡⟨⟨ apV-comp ⟩⟩
              apV (comp up σ) x
            ∎

      open Composition {F} {F} {F} comp liftOp-comp apV-comp renaming (liftOp'-circ to liftOp'-comp;ap-circ to ap-comp;circ-cong to comp-cong) public
\end{code}

\newcommand{\Op}{\ensuremath{\mathbf{Op}}}

The extend'bets and operations up to equivalence form
a category, which we denote $\Op$.
The action of application associates, with every operator family, a functor $\Op \rightarrow \Set$,
which maps an extend'bet $U$ to the set of expressions over $U$, and every operation $\sigma$ to the function $\sigma[-]$.
This functor is faithful and injective on objects, and so $\Op$ can be seen as a subcategory of $\Set$.

\begin{code}
      assoc : ∀ {U} {V} {W} {X} {τ : Op W X} {σ : Op V W} {ρ : Op U V} → comp τ (comp σ ρ) ∼op comp (comp τ σ) ρ
      assoc {U} {V} {W} {X} {τ} {σ} {ρ} {K} x = let open ≡-Reasoning {A = Expression X (varKind K)} in 
          begin 
            apV (comp τ (comp σ ρ)) x
          ≡⟨ apV-comp ⟩
            ap τ (apV (comp σ ρ) x)
          ≡⟨ cong (ap τ) apV-comp ⟩
            ap τ (ap σ (apV ρ x))
          ≡⟨⟨ ap-comp (apV ρ x) ⟩⟩
            ap (comp τ σ) (apV ρ x)
          ≡⟨⟨ apV-comp ⟩⟩
            apV (comp (comp τ σ) ρ) x
          ∎

      unitl : ∀ {U} {V} {σ : Op U V} → comp (idOp V) σ ∼op σ
      unitl {U} {V} {σ} {K} x = let open ≡-Reasoning {A = Expression V (varKind K)} in 
          begin 
            apV (comp (idOp V) σ) x
          ≡⟨ apV-comp ⟩
            ap (idOp V) (apV σ x)
          ≡⟨ ap-idOp ⟩
            apV σ x
          ∎

      unitr : ∀ {U} {V} {σ : Op U V} → comp σ (idOp U) ∼op σ
      unitr {U} {V} {σ} {K} x = let open ≡-Reasoning {A = Expression V (varKind K)} in
          begin 
            apV (comp σ (idOp U)) x
          ≡⟨ apV-comp ⟩
            ap σ (apV (idOp U) x)
          ≡⟨ cong (ap σ) (apV-idOp x) ⟩
            apV σ x
          ∎

  record OpFamily : Set₂ where
      field
        liftFamily : LiftFamily
        isOpFamily  : IsOpFamily liftFamily
      open IsOpFamily isOpFamily public
\end{code}

\subsection{Replacement}

The operation family of \emph{replacement} is defined as follows.  A replacement $\rho : U \rightarrow V$ is a function
that maps every variable in $U$ to a variable in $V$ of the same kind.  Application, idOpentity and composition are simply
function application, the idOpentity function and function composition.  The successor is the canonical injection $V \rightarrow (V, K)$,
and $(\sigma , K)$ is the extension of $\sigma$ that maps $x_0$ to $x_0$.

\begin{code}
  Rep : Alphabet → Alphabet → Set
  Rep U V = ∀ K → Var U K → Var V K

  Rep↑ : ∀ {U} {V} K → Rep U V → Rep (U , K) (V , K)
  Rep↑ _ _ _ x₀ = x₀
  Rep↑ _ ρ K (↑ x) = ↑ (ρ K x)

  upRep : ∀ {V} {K} → Rep V (V , K)
  upRep _ = ↑

  idOpRep : ∀ V → Rep V V
  idOpRep _ _ x = x

  pre-replacement : PreOpFamily
  pre-replacement = record { 
      Op = Rep; 
      apV = λ ρ x → var (ρ _ x); 
      up = upRep; 
      apV-up = refl; 
      idOp = idOpRep; 
      apV-idOp = λ _ → refl }

  _∼R_ : ∀ {U} {V} → Rep U V → Rep U V → Set
  _∼R_ = PreOpFamily._∼op_ pre-replacement

  Rep↑-cong : ∀ {U} {V} {K} {ρ ρ' : Rep U V} → ρ ∼R ρ' → Rep↑ K ρ ∼R Rep↑ K ρ'
  Rep↑-cong ρ-is-ρ' x₀ = refl
  Rep↑-cong ρ-is-ρ' (↑ x) = cong (var ∘ ↑) (var-inj (ρ-is-ρ' x))

  proto-replacement : LiftFamily
  proto-replacement = record { 
      preOpFamily = pre-replacement ; 
      lifting = record { 
        liftOp = Rep↑ ; 
        liftOp-cong = Rep↑-cong } ; 
      isLiftFamily = record { 
        liftOp-x₀ = refl ; 
        liftOp-↑ = λ _ → refl } }

  infix 60 _〈_〉
  _〈_〉 : ∀ {U} {V} {C} {K} → Subexpression U C K → Rep U V → Subexpression V C K
  E 〈 ρ 〉 = LiftFamily.ap proto-replacement ρ E

  infixl 75 _•R_
  _•R_ : ∀ {U} {V} {W} → Rep V W → Rep U V → Rep U W
  (ρ' •R ρ) K x = ρ' K (ρ K x)

  Rep↑-comp : ∀ {U} {V} {W} {K} {ρ' : Rep V W} {ρ : Rep U V} → Rep↑ K (ρ' •R ρ) ∼R Rep↑ K ρ' •R Rep↑ K ρ
  Rep↑-comp x₀ = refl
  Rep↑-comp (↑ _) = refl

  replacement : OpFamily
  replacement = record { 
      liftFamily = proto-replacement ; 
      isOpFamily = record { 
        comp = _•R_ ; 
        apV-comp = refl ; 
        liftOp-comp = Rep↑-comp } }

  rep-cong : ∀ {U} {V} {C} {K} {E : Subexpression U C K} {ρ ρ' : Rep U V} → ρ ∼R ρ' → E 〈 ρ 〉 ≡ E 〈 ρ' 〉
  rep-cong {U} {V} {C} {K} {E} {ρ} {ρ'} ρ-is-ρ' = OpFamily.ap-congl replacement E ρ-is-ρ'

  rep-idOp : ∀ {V} {C} {K} {E : Subexpression V C K} → E 〈 idOpRep V 〉 ≡ E
  rep-idOp = OpFamily.ap-idOp replacement

  rep-comp : ∀ {U} {V} {W} {C} {K} {E : Subexpression U C K} {ρ : Rep U V} {σ : Rep V W} →
      E 〈 σ •R ρ 〉 ≡ E 〈 ρ 〉 〈 σ 〉
  rep-comp {U} {V} {W} {C} {K} {E} {ρ} {σ} = OpFamily.ap-comp replacement E

  Rep↑-idOp : ∀ {V} {K} → Rep↑ K (idOpRep V) ∼R idOpRep (V , K)
  Rep↑-idOp = OpFamily.liftOp-idOp replacement
--TODO Inline many of these
\end{code}

This providOpes us with the canonical mapping from an expression over $V$ to an expression over $(V , K)$:
\begin{code}
  liftE : ∀ {V} {K} {L} → Expression V L → Expression (V , K) L
  liftE E = E 〈 upRep 〉
--TOOD Inline this
\end{code}

\subsection{Substitution}

A \emph{substitution} $\sigma$ from extend'bet $U$ to extend'bet $V$, $\sigma : U \Rightarrow V$, is a function $\sigma$ that maps every variable $x$ of kind $K$ in $U$ to an
\emph{expression} $\sigma(x)$ of kind $K$ over $V$.  We now aim to prov that the substitutions form a family of operations, with application and idOpentity being simply function application and idOpentity.

\begin{code}
  Sub : Alphabet → Alphabet → Set
  Sub U V = ∀ K → Var U K → Expression V (varKind K)

  pre-substitution : PreOpFamily
  pre-substitution = record { 
      Op = Sub; 
      apV = λ σ x → σ _ x; 
      up = λ _ x → var (↑ x); 
      apV-up = refl; 
      idOp = λ _ _ → var; 
      apV-idOp = λ _ → refl }

  open PreOpFamily pre-substitution using () renaming (_∼op_ to _∼_;idOp to idOpSub) public

  Sub↑ : ∀ {U} {V} K → Sub U V → Sub (U , K) (V , K)
  Sub↑ _ _ _ x₀ = var x₀
  Sub↑ _ σ K (↑ x) = (σ K x) 〈 upRep 〉

  Sub↑-cong : ∀ {U} {V} {K} {σ σ' : Sub U V} → σ ∼ σ' → Sub↑ K σ ∼ Sub↑ K σ'
  Sub↑-cong {K = K} σ-is-σ' x₀ = refl
  Sub↑-cong σ-is-σ' (↑ x) = cong (λ E → E 〈 upRep 〉) (σ-is-σ' x)

  SUB↑ : PreOpFamily.Lifting pre-substitution
  SUB↑ = record { liftOp = Sub↑ ; liftOp-cong = Sub↑-cong }
\end{code}
    
Then, given an expression $E$ of kind $K$ over $U$, we write $E[\sigma]$ for the application of $\sigma$ to $E$, which is the result of substituting $\sigma(x)$ for $x$ for each variable in $E$, avoidOping capture.

\begin{code}    
  infix 60 _⟦_⟧
  _⟦_⟧ : ∀ {U} {V} {C} {K} → Subexpression U C K → Sub U V → Subexpression V C K
  E ⟦ σ ⟧ = PreOpFamily.Lifting.ap SUB↑ σ E

  rep2sub : ∀ {U} {V} → Rep U V → Sub U V
  rep2sub ρ K x = var (ρ K x)

  Rep↑-is-Sub↑ : ∀ {U} {V} {ρ : Rep U V} {K} → rep2sub (Rep↑ K ρ) ∼ Sub↑ K (rep2sub ρ)
  Rep↑-is-Sub↑ x₀ = refl
  Rep↑-is-Sub↑ (↑ _) = refl

  module Substitution where
      open PreOpFamily pre-substitution
      open Lifting SUB↑

      liftOp'-is-liftOp' : ∀ {U} {V} {ρ : Rep U V} {A} → rep2sub (OpFamily.liftOp' replacement A ρ) ∼ liftOp' A (rep2sub ρ)
      liftOp'-is-liftOp' {ρ = ρ} {A = []} = ∼-refl {σ = rep2sub ρ}
      liftOp'-is-liftOp' {U} {V} {ρ} {K ∷ A} = let open EqReasoning (OP _ _) in 
        begin
          rep2sub (OpFamily.liftOp' replacement A (Rep↑ K ρ))
        ≈⟨ liftOp'-is-liftOp' {A = A} ⟩
          liftOp' A (rep2sub (Rep↑ K ρ))
        ≈⟨ liftOp'-cong A Rep↑-is-Sub↑ ⟩
          liftOp' A (Sub↑ K (rep2sub ρ))
        ∎

      rep-is-sub : ∀ {U} {V} {K} {C} (E : Subexpression U K C) {ρ : Rep U V} → E 〈 ρ 〉 ≡ E ⟦ (λ K x → var (ρ K x)) ⟧
      rep-is-sub (var _) = refl
      rep-is-sub (app c E) = cong (app c) (rep-is-sub E)
      rep-is-sub out = refl
      rep-is-sub {U} {V} (_,,_ {A = A} {L = L} E F) {ρ} = cong₂ _,,_ 
        (let open ≡-Reasoning {A = Expression (extend' V A) L} in
        begin 
          E 〈 OpFamily.liftOp' replacement A ρ 〉
        ≡⟨ rep-is-sub E ⟩
          E ⟦ (λ K x → var (OpFamily.liftOp' replacement A ρ K x)) ⟧ 
        ≡⟨ ap-congl E (liftOp'-is-liftOp' {A = A}) ⟩
          E ⟦ liftOp' A (λ K x → var (ρ K x)) ⟧
        ∎)
        (rep-is-sub F)

  open Substitution public

  proto-substitution : LiftFamily
  proto-substitution = record { 
      preOpFamily = pre-substitution ; 
      lifting = SUB↑ ; 
      isLiftFamily = record { liftOp-x₀ = refl ; liftOp-↑ = λ {_} {_} {_} {_} {σ} x → rep-is-sub (σ _ x) } }
\end{code}

Composition is defined by $(\sigma \circ \rho)(x) \equiv \rho(x) [ \sigma ]$.

\begin{code}
  infix 75 _•_
  _•_ : ∀ {U} {V} {W} → Sub V W → Sub U V → Sub U W
  (σ • ρ) K x = ρ K x ⟦ σ ⟧
\end{code}

Most of the axioms of a family of operations are easy to verify.  

\begin{code}
  infix 75 _•₁_
  _•₁_ : ∀ {U} {V} {W} → Rep V W → Sub U V → Sub U W
  (ρ •₁ σ) K x = (σ K x) 〈 ρ 〉

  Sub↑-comp₁ : ∀ {U} {V} {W} {K} {ρ : Rep V W} {σ : Sub U V} → Sub↑ K (ρ •₁ σ) ∼ Rep↑ K ρ •₁ Sub↑ K σ
  Sub↑-comp₁ {K = K} x₀ = refl
  Sub↑-comp₁ {U} {V} {W} {K} {ρ} {σ} {L} (↑ x) = let open ≡-Reasoning {A = Expression (W , K) (varKind L)} in 
      begin 
        (σ L x) 〈 ρ 〉 〈 upRep 〉
      ≡⟨⟨ rep-comp {E = σ L x} ⟩⟩
        (σ L x) 〈 upRep •R ρ 〉
      ≡⟨⟩
        (σ L x) 〈 Rep↑ K ρ •R upRep 〉
      ≡⟨ rep-comp {E = σ L x} ⟩
        (σ L x) 〈 upRep 〉 〈 Rep↑ K ρ 〉
      ∎

  sub-comp₁ : ∀ {U} {V} {W} {C} {K} {E : Subexpression U C K} {ρ : Rep V W} {σ : Sub U V} →
      E ⟦ ρ •₁ σ ⟧ ≡ E ⟦ σ ⟧ 〈 ρ 〉
  sub-comp₁ {E = E} = Composition.ap-circ {proto-replacement} {proto-substitution} {proto-substitution} 
                  _•₁_ Sub↑-comp₁ refl E

  infix 75 _•₂_
  _•₂_ : ∀ {U} {V} {W} → Sub V W → Rep U V → Sub U W
  (σ •₂ ρ) K x = σ K (ρ K x)

  Sub↑-comp₂ : ∀ {U} {V} {W} {K} {σ : Sub V W} {ρ : Rep U V} → Sub↑ K (σ •₂ ρ) ∼ Sub↑ K σ •₂ Rep↑ K ρ
  Sub↑-comp₂ {K = K} x₀ = refl
  Sub↑-comp₂ (↑ x) = refl

  sub-comp₂ : ∀ {U} {V} {W} {C} {K} {E : Subexpression U C K} {σ : Sub V W} {ρ : Rep U V} → E ⟦ σ •₂ ρ ⟧ ≡ E 〈 ρ 〉 ⟦ σ ⟧
  sub-comp₂ {E = E} = Composition.ap-circ {proto-substitution} {proto-replacement} {proto-substitution} 
                  _•₂_ Sub↑-comp₂ refl E

  Sub↑-comp : ∀ {U} {V} {W} {ρ : Sub U V} {σ : Sub V W} {K} → Sub↑ K (σ • ρ) ∼ Sub↑ K σ • Sub↑ K ρ
  Sub↑-comp x₀ = refl
  Sub↑-comp {W = W} {ρ = ρ} {σ = σ} {K = K} {L} (↑ x) = 
      let open ≡-Reasoning {A = Expression (W , K) (varKind L)} in 
      begin 
        (ρ L x) ⟦ σ ⟧ 〈 upRep 〉
      ≡⟨⟨ sub-comp₁ {E = ρ L x} ⟩⟩
        ρ L x ⟦ upRep •₁ σ ⟧  
      ≡⟨ sub-comp₂ {E = ρ L x} ⟩
        (ρ L x) 〈 upRep 〉 ⟦ Sub↑ K σ ⟧ 
      ∎

  substitution : OpFamily
  substitution = record { 
      liftFamily = proto-substitution ; 
      isOpFamily = record { 
        comp = _•_ ; 
        apV-comp = refl ; 
        liftOp-comp = Sub↑-comp } }
\end{code}

Replacement is a special case of substitution:
\begin{lemma}
Let $\rho$ be a replacement $U \rightarrow V$.
\begin{enumerate}
\item
The replacement $(\rho , K)$ and the substitution $(\rho , K)$ are equal.
\item
$$ E \langle \rho \rangle \equiv E [ \rho ] $$
\end{enumerate}
\end{lemma}

\begin{code}
  open OpFamily substitution using (assoc) renaming (liftOp-idOp to Sub↑-idOp;ap-idOp to sub-idOp;ap-comp to sub-comp;ap-congl to sub-cong;unitl to sub-unitl;unitr to sub-unitr) public
\end{code}

Let $E$ be an expression of kind $K$ over $V$.  Then we write $[x_0 := E]$ for the following substitution
$(V , K) \Rightarrow V$:

\begin{code}
  x₀:= : ∀ {V} {K} → Expression V (varKind K) → Sub (V , K) V
  x₀:= E _ x₀ = E
  x₀:= E K₁ (↑ x) = var x
\end{code}

\begin{lemma}
\begin{enumerate}
\item
$$ \rho \bullet_1 [x_0 := E] \sim [x_0 := E \langle \rho \rangle] \bullet_2 (\rho , K) $$
\item
$$ \sigma \bullet [x_0 := E] \sim [x_0 := E[\sigma]] \bullet (\sigma , K) $$
\end{enumerate}
\end{lemma}

\begin{code}
  comp₁-botsub : ∀ {U} {V} {K} {E : Expression U (varKind K)} {ρ : Rep U V} →
      ρ •₁ (x₀:= E) ∼ (x₀:= (E 〈 ρ 〉)) •₂ Rep↑ K ρ
  comp₁-botsub x₀ = refl
  comp₁-botsub (↑ _) = refl

  comp-botsub : ∀ {U} {V} {K} {E : Expression U (varKind K)} {σ : Sub U V} →
      σ • (x₀:= E) ∼ (x₀:= (E ⟦ σ ⟧)) • Sub↑ K σ
  comp-botsub x₀ = refl
  comp-botsub {σ = σ} {L} (↑ x) = trans (sym sub-idOp) (sub-comp₂ {E = σ L x})
\end{code}

\subsection{Congruences}

A \emph{congruence} is a relation $R$ on expressions such that:
\begin{enumerate}
\item
if $M R N$, then $M$ and $N$ have the same kind;
\item
if $M_i R N_i$ for all $i$, then $c[[\vec{x_1}]M_1, \ldots, [\vec{x_n}]M_n] R c[[\vec{x_1}]N_1, \ldots, [\vec{x_n}]N_n]$.
\end{enumerate}

\begin{code}
  Relation : Set₁
  Relation = ∀ {V} {C} {K} → Subexpression V C K → Subexpression V C K → Set

  record IsCongruence (R : Relation) : Set where
    field
        ICapp : ∀ {V} {K} {C} {c} {MM NN : Body V {K} C} → R MM NN → R (app c MM) (app c NN)
        ICout : ∀ {V} {K} → R {V} { -Constructor K} {out} out out
        ICappl : ∀ {V} {K} {A} {L} {C} {M N : Expression (extend' V A) L} {PP : Body V {K} C} → R M N → R (_,,_ {A = A} M PP) (N ,, PP)
        ICappr : ∀ {V} {K} {A} {L} {C} {M : Expression (extend' V A) L} {NN PP : Body V {K} C} → R NN PP → R (_,,_ {A = A} M NN) (M ,, PP)
\end{code}

\subsection{Contexts}

A \emph{context} has the form $x_1 : A_1, \ldots, x_n : A_n$ where, for each $i$:
\begin{itemize}
\item $x_i$ is a variable of kind $K_i$ distinct from $x_1$, \ldots, $x_{i-1}$;
\item $A_i$ is an expression of some kind $L_i$;
\item $L_i$ is a parent of $K_i$.
\end{itemize}
The \emph{domain} of this context is the extend'bet $\{ x_1, \ldots, x_n \}$.

We give ourselves the following operations.  Given an extend'bet $A$ and finite set $F$, let $\mathsf{extend}\ A\ K\ F$ be the
extend'bet $A \uplus F$, where each element of $F$ has kind $K$.  Let $\mathsf{embedr}$ be the canonical injection
$F \rightarrow \mathsf{extend}\ A\ K\ F$; thus, for all $x \in F$, we have $\mathsf{embedr}\ x$ is a variable
of $\mathsf{extend}\ A\ K\ F$ of kind $K$.

\begin{code}
  extend : Alphabet → VarKind → ℕ → Alphabet
  extend A K zero = A
  extend A K (suc F) = extend A K F , K

  embedr : ∀ {A} {K} {F} → Fin F → Var (extend A K F) K
  embedr zero = x₀
  embedr (suc x) = ↑ (embedr x)
\end{code}

Let $\mathsf{embedl}$ be the canonical injection $A \rightarrow \mathsf{extend}\ A\ K\ F$, which
is a replacement.

\begin{code}
  embedl : ∀ {A} {K} {F} → Rep A (extend A K F)
  embedl {F = zero} _ x = x
  embedl {F = suc F} K x = ↑ (embedl {F = F} K x)
\end{code}

\begin{code}
  data Context (K : VarKind) : Alphabet → Set where
      〈〉 : Context K ∅
      _,_ : ∀ {V} → Context K V → Expression V (parent K) → Context K (V , K)

  typeof : ∀ {V} {K} (x : Var V K) (Γ : Context K V) → Expression V (parent K)
  typeof x₀ (_ , A) = A 〈 upRep 〉
  typeof (↑ x) (Γ , _) = typeof x Γ 〈 upRep 〉

  data Context' (A : Alphabet) (K : VarKind) : ℕ → Set where
      〈〉 : Context' A K zero
      _,_ : ∀ {F} → Context' A K F → Expression (extend A K F) (parent K) → Context' A K (suc F)
    
  typeof' : ∀ {A} {K} {F} → Fin F → Context' A K F → Expression (extend A K F) (parent K)
  typeof' zero (_ , A) = A 〈 upRep 〉
  typeof' (suc x) (Γ , _) = typeof' x Γ 〈 upRep 〉

record Grammar' : Set₁ where
  field
    taxonomy : Taxonomy
    toGrammar : ToGrammar' taxonomy
  open Taxonomy taxonomy public
  open ToGrammar' toGrammar public
\end{code}
