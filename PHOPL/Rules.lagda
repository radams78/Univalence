\AgdaHide{
\begin{code}
module PHOPL.Rules where
open import PHOPL.Grammar
open import PHOPL.Red

infix 10 _⊢_∶_
data valid : ∀ {V} → Context V → Set
data _⊢_∶_ : ∀ {V} {K} → Context V → 
  Expression V (varKind K) → 
  Expression V (parent K) → Set
\end{code}
}

\mode<article>{The rules of deduction of the system
are as follows.

$$ \infer{\langle \rangle \vald}{} \qquad
\infer{\Gamma, x : A \vald}{\Gamma \vald} \qquad 
\infer{\Gamma, p : \phi \vald}{\Gamma \vdash \phi : \Omega} $$

$$ \infer[(x : A \in \Gamma)]{\Gamma \vdash x : A}{\Gamma \vald} \qquad
\infer[(p : \phi \in \Gamma)]{\Gamma \vdash p : \phi}{\Gamma \vald} x$$}

\[ \infer{\Gamma \vdash \bot : \Omega}{\Gamma \vald} \qquad
\infer{\Gamma \vdash \phi \rightarrow \psi : \Omega}{\Gamma \vdash \phi : \Omega \quad \Gamma \vdash \psi : \Omega} \]

\[ \infer{\Gamma \vdash \delta \epsilon : \psi} {\Gamma \vdash \delta : \phi \rightarrow \psi \quad \Gamma \vdash \epsilon : \phi} \]

\[ \infer{\Gamma \vdash \lambda p : \phi . \delta : \phi \rightarrow \psi}{\Gamma, p : \phi \vdash \delta : \psi} \]

\mode<article>{$$ \infer[(\phi \simeq \phi)]{\Gamma \vdash \delta : \psi}{\Gamma \vdash \delta : \phi \quad \Gamma \vdash \psi : \Omega} y$$}

\begin{code}
data valid where
  empR : 

  -----------
    valid 〈〉

  ctxTR : ∀ {V} {Γ : Context V} {A : Type} → 

      valid Γ → 
  ------------------
    valid (Γ ,T A)

  ctxPR : ∀ {V} {Γ : Context V} {φ : Term V} → 

     Γ ⊢ φ ∶ ty Ω → 
  ------------------
    valid (Γ ,P φ)

  ctxER : ∀ {V} {Γ : Context V} {M N : Term V} {A : Type} →

    Γ ⊢ M ∶ ty A → Γ ⊢ N ∶ ty A → 
  --------------------------------
        valid (Γ ,E M ≡〈 A 〉 N)
\end{code}

\begin{frame}[fragile]
\frametitle{Simply-Typed Lambda Calculus}
\begin{code}
data _⊢_∶_ where
\end{code}

\mode<beamer>{We begin with the simply-typed lambda calculus (no surprises so far):

$$
\begin{array}{lrcl}
\text{Type} & A & ::= & \Omega \mid A \rightarrow A \\
\text{Term} & M,\phi & ::= & x \mid \lambda x:A.M \mid M M
\end{array}
$$

\[ \infer{\Gamma \vdash \lambda x:A.M : A \rightarrow B}{\Gamma, x : A \vdash M : B} \qquad
\infer{\Gamma \vdash M N : B} {\Gamma \vdash M : A \rightarrow B \quad \Gamma \vdash N : A} \]
}

\end{frame}

\begin{code}
  varR : ∀ {V} {K} {Γ : Context V} (x : Var V K)

      (validΓ : valid Γ)     → 
  -------------------------
    Γ ⊢ var x ∶ typeof x Γ

  appR : ∀ {V} {Γ : Context V} {M N : Term V} {A} {B} 

    (Γ⊢M∶A⇛B : Γ ⊢ M ∶ ty (A ⇛ B)) (Γ⊢N∶A : Γ ⊢ N ∶ ty A) →
  ----------------------------------------------------------
                  Γ ⊢ appT M N ∶ ty B

  ΛR : ∀ {V} {Γ : Context V} {A} {M : Term (V , -Term)} {B}
    (Γ,A⊢M∶B : Γ , ty A ⊢ M ∶ ty B) → Γ ⊢ ΛT A M ∶ ty (A ⇛ B)
\end{code}

\begin{frame}[fragile]
\frametitle{Propositional Logic}
$\Omega$ is the universe of propositions:
\[
\begin{array}{lrcl}
\text{Term} & M,\phi & ::= & \cdots \mid \bot \mid \phi \supset \phi \\
\text{Proof} & \delta & ::= & p \mid \lambda p : \phi . \delta \mid \delta \delta
\end{array}
\]
\[ \infer{\Gamma \vdash \delta \epsilon : \psi} {\Gamma \vdash \delta : \phi \rightarrow \psi \quad \Gamma \vdash \epsilon : \phi}
\qquad \infer{\Gamma \vdash \lambda p : \phi . \delta : \phi \rightarrow \psi}{\Gamma, p : \phi \vdash \delta : \psi} \]

\[ \infer[(\phi \simeq \phi)]{\Gamma \vdash \delta : \psi}{\Gamma \vdash \delta : \phi \quad \Gamma \vdash \psi : \Omega} \]
\end{frame}

\begin{code}
  ⊥R : ∀ {V} {Γ : Context V}

   (validΓ : valid Γ) →
  --------------------
       Γ ⊢ ⊥ ∶ ty Ω

  ⊃R : ∀ {V} {Γ : Context V} {φ ψ : Term V}

    (Γ⊢φ∶Ω : Γ ⊢ φ ∶ ty Ω) (Γ⊢ψ∶Ω : Γ ⊢ ψ ∶ ty Ω) →
  ------------------------------------------
                 Γ ⊢ φ ⊃ ψ ∶ ty Ω

  appPR : ∀ {V} {Γ : Context V} {δ ε : Proof V} {φ ψ : Term V} →
    Γ ⊢ δ ∶ φ ⊃ ψ → Γ ⊢ ε ∶ φ → Γ ⊢ appP δ ε ∶ ψ
  ΛPR : ∀ {V} {Γ : Context V} {δ : Proof (V , -Proof)} {φ ψ : Term V} → 
    Γ ,P φ ⊢ δ ∶ ψ 〈 upRep 〉 → Γ ⊢ ΛP φ δ ∶ φ ⊃ ψ
  convR : ∀ {V} {Γ : Context V} {δ : Proof V} {φ ψ : Term V} →
    Γ ⊢ δ ∶ φ → Γ ⊢ ψ ∶ ty Ω → φ ≃ ψ → Γ ⊢ δ ∶ ψ
\end{code}

\begin{frame}
\frametitle{Extensional Equality}
\onslide<1>{On top of this we add extensional equality.}

\[ \begin{array}{lrcl}
\text{Path} & P & ::= & e \onslide<2->{\mid \reff{M} \mid \univ{\phi}{\phi}{P}{P}} \onslide<4->{\mid P \supset^* P \mid} \\
& & & \onslide<4->{PP} \onslide<5->{\mid \triplelambda e : x =_A x . P} \\
\text{Proof} & \delta & ::= & \cdots \onslide<3->{\mid P^+ \mid P^-}
\end{array}
\]

\only<2>{Two main ways to prove equality:

\[ \infer{\Gamma \vdash \reff{M} : M =_A M}{\Gamma \vdash M : A} \qquad
\infer{\Gamma \vdash \univ{\phi}{\psi}{\delta}{\epsilon} : \phi =_\Omega \psi}{\Gamma \vdash \delta : \phi \rightarrow \psi \quad \Gamma \vdash \epsilon : \psi \rightarrow \phi} \]}

\mode<article>{$$ \infer{\Gamma, e : M =_A N \vald}{\Gamma \vdash M : A \quad \Gamma \vdash N : A}
\qquad
\infer[e : M =_A N \in \Gamma]{\Gamma \vdash e : M =_A N}{\Gamma \vald} $$
}

\only<3>{We can eliminate equalities in $\Omega$:
\[ 
\qquad
\infer{\Gamma \vdash P^+ : \phi \rightarrow \psi}{\Gamma \vdash P : \phi =_\Omega \psi}
\qquad
\infer{\Gamma \vdash P^- : \psi \rightarrow \phi}{\Gamma \vdash P : \psi =_\Omega \psi} \]
}

\only<5>{Congruence rule for $\lambda$:

\[ \infer{\Gamma \vdash \triplelambda e : x =_A y . P : M =_{A \rightarrow B} N}{\Gamma, x : A, y : A, e : x =_A y \vdash M x =_B N y} \]

$e$, $x$ and $y$ are bound within $P$.
}

\onslide<4>{Congruence rules and conversion
\[ \infer{\Gamma \vdash P \sup* Q : \phi \sup \psi =_\Omega \phi' \sup \psi'}{\Gamma \vdash P : \phi =_\Omega \phi' \quad \Gamma \vdash Q : \psi =_\Omega \psi'}  \]
\[ \infer{\Gamma \vdash PQ : MN =_B M' N'}{\Gamma \vdash P : M =_{A \rightarrow B} M' \quad \Gamma \vdash Q : N =_A N'} \]
\[ \infer[(M \simeq_\beta M', N \simeq_\beta N')]{\Gamma \vdash P : M' =_A N'}{\Gamma \vdash P : M =_A N \quad \Gamma \vdash M' : A \quad \Gamma \vdash N' : A} \]
}
\end{frame}

\begin{code}
  refR : ∀ {V} {Γ : Context V} {M : Term V} {A : Type} → 

               Γ ⊢ M ∶ ty A → 
  ---------------------------------------
    Γ ⊢ app -ref (M ,, out) ∶ M ≡〈 A 〉 M

  ⊃*R : ∀ {V} {Γ : Context V} {P Q : Expression V (varKind -Path)} {φ φ' ψ ψ' : Term V} →

    Γ ⊢ P ∶ φ ≡〈 Ω 〉 φ' → Γ ⊢ Q ∶ ψ ≡〈 Ω 〉 ψ' →
  ----------------------------------------------
      Γ ⊢ P ⊃* Q ∶ (φ ⊃ ψ) ≡〈 Ω 〉 (φ' ⊃ ψ')

  univR : ∀ {V} {Γ : Context V} {δ ε : Proof V} {φ ψ : Term V} →

    Γ ⊢ δ ∶ φ ⊃ ψ → Γ ⊢ ε ∶ ψ ⊃ φ → 
  -----------------------------------
    Γ ⊢ univ φ ψ δ ε ∶ φ ≡〈 Ω 〉 ψ

  plusR : ∀ {V} {Γ : Context V} {P : Expression V (varKind -Path)} {φ ψ : Term V} →

    Γ ⊢ P ∶ φ ≡〈 Ω 〉 ψ → 
  -----------------------
    Γ ⊢ plus P ∶ φ ⊃ ψ

  minusR : ∀ {V} {Γ : Context V} {P : Expression V (varKind -Path)} {φ ψ : Term V} →

    Γ ⊢ P ∶ φ ≡〈 Ω 〉 ψ → 
  -----------------------
    Γ ⊢ minus P ∶ ψ ⊃ φ

  lllR : ∀ {V} {Γ : Context V} {A B : Type} {M N : Term V} 
    {P : Path (V , -Term , -Term , -Path)} →

    Γ ,T A ,T A ,E var x₁ ≡〈 A 〉 var x₀
     ⊢ P ∶ appT (M ⇑ ⇑ ⇑ ) (var x₂) ≡〈 B 〉 appT (N ⇑ ⇑ ⇑) (var x₁) →
  ------------------------------------------------------------------------
                       Γ ⊢ λλλ A P ∶ M ≡〈 A ⇛ B 〉 N

  app*R : ∀ {V} {Γ : Context V} {P Q : Path V} {M M' N N' : Term V} {A B : Type} →

    Γ ⊢ N ∶ ty A → Γ ⊢ N' ∶ ty A →
    Γ ⊢ P ∶ M ≡〈 A ⇛ B 〉 M' → Γ ⊢ Q ∶ N ≡〈 A 〉 N' →
  -------------------------------------------------
    Γ ⊢ app* N N' P Q ∶ appT M N ≡〈 B 〉 appT M' N'

  convER : ∀ {V} {Γ : Context V} {P : Expression V (varKind -Path)} {M M' N N' : Term V} {A : Type}

                                           (Γ⊢P∶M≡N : Γ ⊢ P ∶ M ≡〈 A 〉 N)   (Γ⊢M':A : Γ ⊢ M' ∶ ty A)   (Γ⊢N'∶A : Γ ⊢ N' ∶ ty A)
         (M≃M' : M ≃ M') (N≃N' : N ≃ N') → ------------------------------------------------------------------------------------
                                                                             Γ ⊢ P ∶ M' ≡〈 A 〉 N'
\end{code}

\AgdaHide{
\begin{code}
addpath-valid : ∀ {V} {Γ : Context V} {A} → valid Γ → valid (addpath Γ A)
addpath-valid validΓ = ctxER (varR x₁ (ctxTR (ctxTR validΓ))) 
                             (varR x₀ (ctxTR (ctxTR validΓ)))
\end{code}
}
