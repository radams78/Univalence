\documentclass{easychair}
\bibliographystyle{plain}

\title{A Strongly Normalizing Computation Rule for the Univalence Axiom in Higher-Order Propositional Logic}
\author{Robin Adams\inst{1} \and Marc Bezem\inst{1} \and Thierry Coquard\inst{2}}
\institute{Universitetet i Bergen,
Bergen, Norway \\
\email{\{robin.adams,marc\}@uib.no}
\and
University of Gothenburg,
Gothenburg, Sweden \\
\email{coquand@chalmers.se}}
\titlerunning{Strongly Normalizang Computation Rule for Univalence}
\authorrunning{R. Adams, M. Bezem, T. Coquand}

\usepackage{proof}
\usepackage{amssymb}
\usepackage{amsthm}

\newcommand{\vald}{\ \mathrm{valid}}
\newcommand{\univ}[4]{\mathsf{univ}_{{#1},{#2}} \left( {#3} , {#4} \right)}
\newcommand{\triplelambda}{\lambda \!\! \lambda \!\! \lambda}
\newcommand{\reff}[1]{\mathsf{ref} \left( {#1} \right)}
\newcommand{\eqdef}{\stackrel{\mathrm{def}}{=}}
\newcommand{\SN}{\mathbf{SN}}

\newtheorem{lemma}{Lemma}
\newtheorem{theorem}{Theorem}

\begin{document}

\maketitle

Homotopy type theory offers the promise of a formal system for the univalent foundations of mathematics.  However, if
we simply add the univalence axiom to type theory, then we lose the property of canonicity --- that every term computes to
a normal form.  A computation becomes `stuck' when it reaches the point that it needs to evaluate a proof term
that is an application of the univalence axiom.  We wish to find a way to compute with the univalence axiom.

As a first step towards such a system, we present here a system of higher-order propositional logic,  with a universe $\Omega$ of propositions
closed under implication and quantification over any simple type over $\Omega$.  We add a type $a =_A b$ for any terms $a$, $b$ of type $A$
(this type is not a proposition in $\Omega$), and two ways to prove an equality: reflexivity, and the univalence axiom.  We present
reduction relations for this system, and prove the reduction confluent and strongly normalizing.

\section{Syntax and Rules of Deduction}

We call the following type theory predicative higher-order propositional logic.  Its syntax is given by the grammar

\[ \begin{array}{lrcl}
\text{Proof} & \delta & ::= & p \mid \delta \delta \mid \lambda p : \phi . \delta \\
\text{Term} & M, \phi & ::= & x \mid \bot \mid M M \mid \lambda x : A . M \mid \phi \supset \phi \\
\text{Type} & A & ::= & \Omega \mid A \rightarrow A \\
\text{Term Context} & \Gamma & ::= & \langle \rangle \mid \Gamma , x : A \\
\text{Proof Context} & \Delta & ::= & \langle \rangle \mid \Delta, p : \phi \\
\text{Judgement} & \mathcal{J} & ::= & \Gamma \vald \mid \Gamma \vdash M : A \mid \Gamma, \Delta \vald \mid \Gamma, \Delta \vdash \delta : \phi 
\end{array} \]

where $p$ is a \emph{proof variable} and $x$ a \emph{term variable}.  Its rules of deduction are

\[ \infer{\langle \rangle \vald}{} \qquad
\infer{\Gamma, x : A \vald}{\Gamma \vald} \qquad 
\infer{\Gamma, p : \phi \vald}{\Gamma \vdash \phi : \Omega} \]

\[ \infer[(x : A \in \Gamma)]{\Gamma \vdash x : A}{\Gamma \vald} \qquad
\infer[(p : \phi \in \Gamma)]{\Gamma \vdash p : \phi}{\Gamma \vald} \]

\[ \infer{\Gamma \vdash \bot : \Omega}{\Gamma \vald} \qquad
\infer{\Gamma \vdash \phi \rightarrow \psi : \Omega}{\Gamma \vdash \phi : \Omega \quad \Gamma \vdash \psi : \Omega} \]

\[ \infer{\Gamma \vdash M N : B} {\Gamma \vdash M : A \rightarrow B \quad \Gamma \vdash N : A} \qquad
\infer{\Gamma \vdash \delta \epsilon : \psi} {\Gamma \vdash \delta : \phi \rightarrow \psi \quad \Gamma \vdash \epsilon : \phi} \]

\[ \infer{\Gamma \vdash \lambda x:A.M : A \rightarrow B}{\Gamma, x : A \vdash M : B} \qquad
\infer{\Gamma \vdash \lambda p : \phi . \delta : \phi \rightarrow \psi}{\Gamma, p : \phi \vdash \delta : \psi} \]

\[ \infer[(\phi \simeq \phi)]{\Gamma \vdash \delta : \psi}{\Gamma \vdash \delta : \phi \quad \Gamma \vdash \psi : \Omega} \]

\subsection{Extensional Equality}

On top of this system, we add an extensional equality relation.  We extend the grammar with

\[
\begin{array}{lrcl}
\text{Path} & P & ::= & e \mid \reff{M} \mid P \supset P \mid \univ{\phi}{\phi}{\delta}{\delta} \mid \triplelambda e : x =_A x . P \mid P P\\
\text{Proof} & \delta & ::= & \cdots \mid P^+ \mid P^- \\
\text{Context} & \Gamma & ::= & \cdots \mid \Gamma, e : M =_A M \\
\text{Judgement} & \mathcal{J} & ::= & \cdots \mid \Gamma \vdash P : M =_A M
\end{array}
\]

Note that, in the path $\triplelambda e : x =_A y . P$, the term variables $x$ and $y$ and the proof variable $e$ are all bound within $P$.

We add the following rules of deduction

\[ \infer{\Gamma, e : M =_A N \vald}{\Gamma \vdash M : A \quad \Gamma \vdash N : A}
\qquad
\infer[e : M =_A N \in \Gamma]{\Gamma \vdash e : M =_A N}{\Gamma \vald} \]

\[ \infer{\Gamma \vdash \reff{M} : M =_A M}{\Gamma \vdash M : A}
\qquad
\infer{\Gamma \vdash P \rightarrow Q : \phi \rightarrow \psi =_\Omega \phi' \rightarrow \psi´}{\Gamma \vdash P : \phi =_\Omega \phi´ \quad \Gamma \vdash Q : \psi =_\Omega \psi´} \]

\[ \infer{\Gamma \vdash \univ{\phi}{\psi}{\delta}{\epsilon} : \phi =_\Omega \psi}{\Gamma \vdash \delta : \phi \rightarrow \psi \quad \Gamma \vdash \epsilon : \psi \rightarrow \phi} 
\qquad
\infer{\Gamma \vdash P^+ : \phi \rightarrow \psi}{\Gamma \vdash P : \phi =_\Omega \psi}
\qquad
\infer{\Gamma \vdash P^- : \psi \rightarrow \phi}{\Gamma \vdash P : \psi =_\Omega \psi} \]

\[ \infer{\Gamma \vdash \triplelambda e : x =_A y . P : M =_{A \rightarrow B} N}{\Gamma, x : A, y : A, e : x =_A y \vdash M x =_B N y} \]

\[ \infer{\Gamma \vdash PQ : MN =_B M' N'}{\Gamma \vdash P : M =_{A \rightarrow B} M' \quad \Gamma \vdash Q : N =_A N'} \]

\[ \infer[(M \simeq_\beta M', N \simeq_\beta N')]{\Gamma \vdash P : M' =_A N'}{\Gamma \vdash P : M =_A N \quad \Gamma \vdash M' : A \quad \Gamma \vdash N' : A} \]

\section{Path Substitution}

Every term in the system is functional; that is, it maps equal terms to equal terms.  That is, if $M : B$ depends on a variable $x : A$ and we have a proof of $N =_A N'$,
then we can construct a proof of $[N/x]M =_B [N'/x]M$.  We call this construction \emph{path substitution}.  The definition is as follows.

Given paths $P_1$, \ldots, $P_n$; term variales $x_1$, \ldots, $x_n$; and a term $M$, define the path $\{ P_1 / x_1, \ldots, P_n / x_n \} M$ as follows.
\begin{align*}
\{ P_1 / x_1, \ldots, P_n / x_n \} x_i & \eqdef P_i \\
\{ P_1 / x_1, \ldots, P_n / x_n \} y & \eqdef \reff{y} & (y \not\equiv x_1, \ldots, x_n) \\
\{ P_1 / x_1, \ldots, P_n / x_n \} \bot & \eqdef \reff{\bot} \\
\{ \vec{P} / \vec{x} \} (MN) & \eqdef \{ \vec{P} / \vec{x} \} M \{ \vec{P} / \vec{x} \} N \\
\{ \vec{P} / \vec{x} \} (\lambda y : A . M) & \eqdef \triplelambda e : a =_A a' . \{ \vec{P} / \vec{x} , e / y \} M \\
\{ \vec{P} / \vec{x} \} (\phi \rightarrow \psi) & \eqdef \{ \vec{P} / \vec{x} \} \phi \rightarrow \{ \vec{P} / \vec{x} \} \psi
\end{align*}

\begin{lemma}
If $\Gamma, x_1 : A_1, \ldots, x_n : A_n \vdash M : B$ and $\Gamma \vdash P_i : N_i =_{A_i} N_i'$ for $i = 1, \ldots, n$, then
$\Gamma \vdash \{ \vec{P} / \vec{x} \} M : [ \vec{N} / \vec{x} ] M =_B [ \vec{N'} / \vec{x} ] M$.
\end{lemma}

We also define $M \bullet P$ to be $\{ P / x \} (Mx)$.  Thus, if $M : A \rightarrow B$ and $P : N =_A N'$, then $M \bullet P : MN =_B MN'$.

\section{The Reduction Relation}

We define the following reduction relation on proofs and equality proofs.

\begin{gather*}
(\reff{\phi})^+ \rightsquigarrow \lambda x : \phi . x
\qquad
(\reff{\phi})^- \rightsquigarrow \lambda x : \phi . x
\qquad
\univ{\phi}{\psi}{\delta}{\epsilon}^+ \rightsquigarrow \delta
\qquad
\univ{\phi}{\psi}{\delta}{\epsilon}^- \rightsquigarrow \epsilon
\\
(\reff \phi \rightarrow \univ{\psi}{\chi}{\delta}{\epsilon}) \rightsquigarrow \univ{\phi \rightarrow \psi}{\phi \rightarrow \chi}{\lambda f : \phi \rightarrow \psi . \lambda x : \phi . \delta (f x)}{\lambda g : \phi \rightarrow \chi . \lambda x : \phi . \epsilon (g x)}
\\
(\univ{\phi}{\psi}{\delta}{\epsilon} \rightarrow \reff{\chi}) \rightsquigarrow \univ{\phi \rightarrow \chi}{\psi \rightarrow \chi}{\lambda f : \phi \rightarrow \chi. \lambda x : \psi . f (\epsilon x)}{\lambda g : \psi \rightarrow \chi . \lambda x : \phi . g (\delta x)}
\\
(\univ{\phi}{\psi}{\delta}{\epsilon} \rightarrow \univ{\phi'}{\psi'}{\delta'}{\epsilon'} \rightsquigarrow \univ{\phi \rightarrow \phi'}{\psi \rightarrow \psi'}
{\lambda f : \phi \rightarrow \phi' . \lambda x : \psi . \delta' (f (\epsilon x))}{\lambda g : \psi \rightarrow \psi' . \lambda y : \phi . \epsilon' (g (\delta y))}
\\
(\reff{\phi} \rightarrow \reff{\psi}) \rightsquigarrow \reff{\phi \rightarrow \psi}
\qquad
\reff{M} \reff{N} \rightsquigarrow \reff{MN}
\\
(\reff{\lambda x:A.M})P \rightsquigarrow \{ P / x \} M
\qquad
(\triplelambda e : x =_A y.P)Q \rightsquigarrow [M/x, N/y, Q/e]P
\end{gather*}
where, in the last clause, we have $Q : M =_A N$.
%TODO Fix this

\section{Proof of Strong Normalization}

The proof of strong normalization follows the method of Tait \cite{Tait1967}
We define the set of \emph{computable} proofs of each term, terms of each type
and paths of each equation (in a context $\Gamma$) as follows.

\begin{align*}
E_\Gamma(\Omega) & \eqdef \{ M \mid \Gamma \vdash M : \Omega, M \in \SN \} \\
E_\Gamma(A \rightarrow B) & \eqdef \{ M \mid \Gamma \vdash M : A \rightarrow B, M \in \SN,
& \forall N \in E_\Gamma(A). MN \in E_\Gamma(B), \\
& \forall N, N' \in E_\Gamma(A). \forall P \in E_\Gamma(N =_A N´). M \bullet P \in E_\Gamma(MN =_B MN') \} \\
E_\Gamma(\bot) & \eqdef \{ \delta \mid \Gamma \vdash \delta : \bot, \delta \in \SN \} \\
E_\Gamma(\phi \rightarrow \psi) & \eqdef \{ \delta \mid \Gamma \vdash \delta : \phi \rightarrow \psi, \delta \in \SN, \\
& \forall \epsilon \in E_\Gamma(\phi). \delta \epsilon \in E_\Gamma(\psi) \} \\
E_\Gamma(\phi) & \eqdef E_\Gamma(nf(\phi)) & (\phi \mbox{ a normalizable term of type $\Omega$}) \\
E_\Gamma(\phi =_\Omega \psi) & \eqdef \{ P \mid \Gamma \vdash P : \phi =_\Omega \psi, P \in \SN, \\
& P^+ \in E_\Gamma(\phi \rightarrow \psi), P^- \in E_\Gamma(\psi \rightarrow \phi) \} \\
E_\Gamma(M =_{A \rightarrow B} M') & \eqdef \{ P \mid \Gamma \vdash P : M =_{A \rightarrow B} M', P \in \SN, \\
& \forall N, N' \in E_\Gamma(A), Q \in E_\Gamma(N =_A N'). PQ \in E_\Gamma(MN =_B M'N') \}
\end{align*}

A \emph{computable substitution} $\sigma : \Gamma \rightarrow \Delta$ is a function mapping variables to terms such that,
for every $x : A$ in $\Gamma$, we have $\Delta \vdash \sigma(x) : A$.

A \emph{path} between computable substitutions $\rho : \sigma \rightarrow \sigma' : \Gamma \rightarrow \Delta$ is a function mapping
variables to paths such that, for every $x : A$ in $\Gamma$, we have $\Delta \vdash \rho(x) : \sigma(x) =_A \sigma´(x)$.

Our main theorem is the following:

\begin{theorem}
\begin{enumerate}
\item
If $\sigma : \Gamma \rightarrow \Delta$ and $\Delta \vdash M : A$, then $\sigma M \in E_\Gamma(A)$.
\item
If $\sigma : \Gamma \rightarrow \Delta$ and $\Delta \vdash P : M =_A N$, then $\sigma P \in E_\Gamma(\sigma M =_A \sigma N)$.
\item
If $\rho : \sigma \rightarrow \sigma' : \Gamma \rightarrow \Delta$ and $\Delta \vdash M : A$, then $\rho M \in E_\Gamma(\sigma M =_A \sigma' M)$.
\end{enumerate}
\end{theorem}

This is proven by induction on derivations.  The difficult part is proving that each term constructed is strongly normalizing.  Tait's proof used confluence, which is not available to us here.  Our reduction relation is not confluent in general.  However, it is confluent on the computable terms.  It turns out that, with this result, the induction hypothesis always gives us
confluence of the terms required.

The remainder of the proof is straightforward: the substitution $id$ mapping $x$ to $x$ is a computable substitution.
Hence, if $\Gamma \vdash M : A$, then $id \, M \equiv M$ is computable, hence in $\SN$; and if $\Gamma \vdash P : M = N : A$ then $id \, P \equiv P$ is computable, hence in $\SN$.

\section{Future Work}

In the future, we wish to extend this work in several directions.  We wish to add constructions $\mathsf{sym}(P)$ and $\mathsf{trans}(P,Q)$ that make our equality into an equivalence
relation, and provide reduction rules for each of these.  We wish to extend our logic by placing the equations $M =_A N$ inside $\Omega$, and allow quantification over any type in $A$ (including $\Omega$) in our logic.  This would move our system ever closer to homotopy type theory.  Our ultimate goal is to provide a strongly normalizing reduction relation for homotopy type theory, including the terms involving the univalence axiom, and we believe we have taken the first step.

\bibliography{type}

\end{document}