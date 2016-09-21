\AgdaHide{
\begin{code}
module PHOPL.Rules where
open import PHOPL.Grammar
open import PHOPL.Red
\end{code}
}

\subsection{Rules of Deduction}

The rules of deduction of $\lambda o e$ are given in Figure \ref{fig:lambdaoe}.

\newcommand{\RvarT}{\ensuremath(\mathsf{varT})}
\begin{figure}
\begin{framed}
\paragraph{Contexts}
\[ \infer{\langle \rangle \vald}{} \qquad
\infer{\Gamma, x : A \vald}{\Gamma \vald} \qquad 
\infer{\Gamma, p : \phi \vald}{\Gamma \vdash \phi : \Omega} \qquad
\infer{\Gamma, e : M =_A N \vald}{\Gamma \vdash M : A \quad \Gamma \vdash N : A} \]
\[ \infer[(x : A \in \Gamma)]{\Gamma \vdash x : A}{\Gamma \vald} \qquad
\infer[(p : \phi \in \Gamma)]{\Gamma \vdash p : \phi}{\Gamma \vald} \]
\[ \infer[(e : M =_A N \in \Gamma)]{\Gamma \vdash e : M =_A N}{\Gamma \vald} \]

\paragraph{Terms}
\[ \infer{\Gamma \vdash \bot : \Omega}{\Gamma \vald} \qquad
\infer{\Gamma \vdash \phi \supset \psi : \Omega}{\Gamma \vdash \phi : \Omega \quad \Gamma \vdash \psi : \Omega} \]
\[ \infer{\Gamma \vdash M N : B} {\Gamma \vdash M : A \rightarrow B \quad \Gamma \vdash N : A} \qquad
\infer{\Gamma \vdash \lambda x:A.M : A \rightarrow B}{\Gamma, x : A \vdash M : B} \]

\paragraph{Proofs}
\[ \infer{\Gamma \vdash \delta \epsilon : \psi} {\Gamma \vdash \delta : \phi \supset \psi \quad \Gamma \vdash \epsilon : \phi} \qquad
\infer{\Gamma \vdash \lambda p : \phi . \delta : \phi \supset \psi}{\Gamma, p : \phi \vdash \delta : \psi} \]
\[ \infer[(\phi \simeq \psi)]{\Gamma \vdash \delta : \psi}{\Gamma \vdash \delta : \phi \quad \Gamma \vdash \psi : \Omega} \]

\paragraph{Paths}
\[ \infer{\Gamma \vdash \reff{M} : M =_A M}{\Gamma \vdash M : A}
\qquad
\infer{\Gamma \vdash P \supset^* Q : \phi \supset \psi =_\Omega \phi' \supset \psi'}{\Gamma \vdash P : \phi =_\Omega \phi' \quad \Gamma \vdash Q : \psi =_\Omega \psi'} \]
\[ \infer{\Gamma \vdash \univ{\phi}{\psi}{\delta}{\epsilon} : \phi =_\Omega \psi}{\Gamma \vdash \delta : \phi \supset \psi \quad \Gamma \vdash \epsilon : \psi \supset \phi} 
\qquad
\infer{\Gamma \vdash P^+ : \phi \supset \psi}{\Gamma \vdash P : \phi =_\Omega \psi}
\qquad
\infer{\Gamma \vdash P^- : \psi \supset \phi}{\Gamma \vdash P : \psi =_\Omega \psi} \]
\[ \infer{\Gamma \vdash \triplelambda e : x =_A y . P : M =_{A \rightarrow B} N}
  {\begin{array}{c}
     \Gamma, x : A, y : A, e : x =_A y \vdash P : M x =_B N y \\
     \Gamma \vdash M : A \rightarrow B \quad
\Gamma \vdash N : A \rightarrow B
     \end{array}} \]
\[ \infer{\Gamma \vdash P_{NN'}Q : MN =_B M' N'}{\Gamma \vdash P : M =_{A \rightarrow B} M' \quad \Gamma \vdash Q : N =_A N' \quad \Gamma \vdash N : A \quad \Gamma \vdash N' : A} \]
\[ \infer[(M \simeq M', N \simeq N')]{\Gamma \vdash P : M' =_A N'}{\Gamma \vdash P : M =_A N \quad \Gamma \vdash M' : A \quad \Gamma \vdash N' : A} \]
\end{framed}
\caption{Rules of Deduction of $\lambda oe$}
\label{fig:lambdaoe}
\end{figure}

\begin{code}
infix 10 _⊢_∶_
data valid : ∀ {V} → Context V → Set
data _⊢_∶_ : ∀ {V} {K} → Context V → 
  Expression V (varKind K) → 
  Expression V (parent K) → Set

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

data _⊢_∶_ where

  varR : ∀ {V} {K} {Γ : Context V} (x : Var V K)

      (validΓ : valid Γ)     → 
  ------------------------------
    Γ ⊢ var x ∶ typeof x Γ

  appR : ∀ {V} {Γ : Context V} {M N : Term V} {A} {B} 

    (Γ⊢M∶A⇛B : Γ ⊢ M ∶ ty (A ⇛ B)) (Γ⊢N∶A : Γ ⊢ N ∶ ty A) →
  ----------------------------------------------------------
                  Γ ⊢ appT M N ∶ ty B

  ΛR : ∀ {V} {Γ : Context V} {A} {M : Term (V , -Term)} {B}
    (Γ,A⊢M∶B : Γ , ty A ⊢ M ∶ ty B) → Γ ⊢ ΛT A M ∶ ty (A ⇛ B)

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
    Γ ⊢ φ ∶ ty Ω → Γ ,P φ ⊢ δ ∶ ψ 〈 upRep 〉 → Γ ⊢ ΛP φ δ ∶ φ ⊃ ψ
  convR : ∀ {V} {Γ : Context V} {δ : Proof V} {φ ψ : Term V} →
    Γ ⊢ δ ∶ φ → Γ ⊢ ψ ∶ ty Ω → φ ≃ ψ → Γ ⊢ δ ∶ ψ

  refR : ∀ {V} {Γ : Context V} {M : Term V} {A : Type} → 

               Γ ⊢ M ∶ ty A → 
  ---------------------------------------
    Γ ⊢ reff M ∶ M ≡〈 A 〉 M

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
