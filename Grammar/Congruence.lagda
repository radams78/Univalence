\AgdaHide{
\begin{code}
open import Grammar.Base

module Grammar.Congruence (G : Grammar) where
open Grammar G
\end{code}
}

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
    ICapp : ∀ {V} {K} {C} {c} {MM NN : Body V {K} C} → 
      R MM NN → R (app c MM) (app c NN)
    ICout : ∀ {V} {K} → R {V} { -Constructor K} {out} out out
    ICappl : ∀ {V} {K} {A} {L} {C} 
      {M N : Expression (extend V A) L} {PP : Body V {K} C} → 
      R M N → R (_,,_ {A = A} M PP) (N ,, PP)
    ICappr : ∀ {V} {K} {A} {L} {C}
      {M : Expression (extend V A) L} {NN PP : Body V {K} C} → 
      R NN PP → R (_,,_ {A = A} M NN) (M ,, PP)
\end{code}

\begin{lemma}
If $R$ is a congruence, then so are its reflexive transitive closure, and its reflexive symmetric transitive closure.
\end{lemma}

\begin{code}
data RTC (R : Relation) : Relation where
  RTCI  : ∀ {V} {C} {K} {E F : Subexpression V C K} → R E F → RTC R E F
  ref   : ∀ {V} {C} {K} {E : Subexpression V C K} → RTC R E E
  trans : ∀ {V} {C} {K} {E F G : Subexpression V C K} → RTC R E F → RTC R F G → RTC R E G

module RTC-congruence {R : Relation} (iscongruence : IsCongruence R) where
  open IsCongruence iscongruence

  RTCapp : ∀ {V} {K} {C} {c} {E F : Body V {K} C} → RTC R E F → RTC R (app c E) (app c F)
  RTCapp (RTCI REF) = RTCI (ICapp REF)
  RTCapp ref = ref
  RTCapp (trans RTCEF RTCFG) = trans (RTCapp RTCEF) (RTCapp RTCFG)

  RTCappl : ∀ {V} {A} {L} {K} {C} {E F : Expression (extend V A) L} {G : Body V {K} C} →
    RTC R E F → RTC R (_,,_ {A = A} E G)  (F ,, G)
  RTCappl (RTCI REF) = RTCI (ICappl REF)
  RTCappl ref = ref
  RTCappl (trans RTCEF RTCFG) = trans (RTCappl RTCEF) (RTCappl RTCFG)

  RTCappr : ∀ {V} {A} {L} {K} {C} {E : Expression (extend V A) L} {F G : Body V {K} C} →
    RTC R F G → RTC R (_,,_ {A = A} E F) (E ,, G)
  RTCappr (RTCI RFG) = RTCI (ICappr RFG)
  RTCappr ref = ref
  RTCappr (trans RTCFG RTCGH) = trans (RTCappr RTCFG) (RTCappr RTCGH)

  RTC-congruence : IsCongruence (RTC R)
  RTC-congruence = record { 
    ICapp = RTCapp ; 
    ICout = ref ; 
    ICappl = RTCappl ; 
    ICappr = RTCappr }

data RSTC (R : Relation) : Relation where
  RSTCI : ∀ {V} {C} {K} {E F : Subexpression V C K} → R E F → RSTC R E F
  ref   : ∀ {V} {C} {K} {E : Subexpression V C K} → RSTC R E E
  sym   : ∀ {V} {C} {K} {E F : Subexpression V C K} → RSTC R E F → RSTC R F E
  trans : ∀ {V} {C} {K} {E F G : Subexpression V C K} → RSTC R E F → RSTC R F G → RSTC R E G
